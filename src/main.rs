#[macro_use]
extern crate lalrpop_util;
use builtin_functions::BuiltinFunction;
use lasso::Rodeo;
use runtime::RuntimeCtx;
use rustyline::{error::ReadlineError, Editor};
use shared_child::SharedChild;
use std::{
    path::PathBuf,
    process::{self, ExitStatus},
    str::FromStr,
    sync::{Arc, RwLock},
};
use structopt::StructOpt;

use crate::runtime::RuntimeError;

pub mod ast;
mod builtin_functions;
pub mod cow_ast;
mod editor;
pub mod lexer;
pub mod runtime;
pub mod type_checker;

lalrpop_mod!(pub rsh);

type ShResult<T, E = Error> = std::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("ser/de error: {0}")]
    Serde(#[from] ron::Error),
    #[error("bincode ser/de error: {0}")]
    BinSerde(#[from] bincode::Error),
    #[error("could not decode base64 string: {0}")]
    Base64(#[from] base64::DecodeError),
    #[error("called exit: {0}")]
    Exited(i32),
    #[error("parse error: {0}")]
    Parse(String),
    #[error("type error: expected {expected} got {got}")]
    TypeError { expected: ast::Type, got: ast::Type },
    #[error("runtime error: {0}")]
    RuntimeError(#[from] runtime::RuntimeError),
}

pub struct ShellContext {
    current_process: Arc<RwLock<Option<SharedChild>>>,
    builtins: Vec<BuiltinFunction>,
    last_exit: Option<ExitStatus>,
    rodeo: Rodeo,
}

impl ShellContext {
    pub fn new() -> Self {
        ShellContext {
            current_process: Arc::new(RwLock::new(None)),
            last_exit: None,
            rodeo: Rodeo::new(),
            builtins: builtin_functions::builtins(),
        }
    }
}
macro_rules! report {
    ($e:expr) => {
        match $e {
            Err(e) => color_eyre::eyre::bail!("An error occured: {}", e),
            Ok(v) => v,
        }
    };
}

fn interactive_input(
    sh_ctx: &mut ShellContext,
    prompt_command: Option<&str>,
) -> color_eyre::Result<i32> {
    let mut rl: Editor<editor::Editor> = Editor::with_config(
        rustyline::Config::builder()
            .auto_add_history(true)
            .history_ignore_space(true)
            .tab_stop(4)
            .build(),
    );
    rl.set_helper(Some(editor::Editor::new()));
    match rl.load_history("/home/traxys/.rsh-history") {
        Ok(_) => (),
        Err(ReadlineError::Io(e)) if e.kind() == std::io::ErrorKind::NotFound => (),
        Err(e) => Err(e)?,
    }
    let res = interactive_loop(&mut rl, sh_ctx, prompt_command);
    rl.save_history("/home/traxys/.rsh-history")?;
    res
}

fn interactive_loop<E: rustyline::Helper>(
    rl: &mut rustyline::Editor<E>,
    sh_ctx: &mut ShellContext,
    prompt_command: Option<&str>,
) -> color_eyre::Result<i32> {
    let command_parser = rsh::CommandParser::new();

    let mut rt_ctx = runtime::RuntimeCtx::new(sh_ctx);
    loop {
        let prompt = prompt_command
            .map(|command| -> color_eyre::Result<_> {
                let command = &command;
                let parsed = cow_ast::Command::from_ast(
                    command_parser
                        .parse(rt_ctx.shell_ctx, command, lexer::lexer(&command))
                        .map_err(|err| {
                            color_eyre::eyre::eyre!("could not parse prompt: {}", err)
                        })?,
                    rt_ctx.shell_ctx,
                )?;
                let mut cmd = rt_ctx.prepare_cmd(&parsed)?;
                cmd.output()
                    .map(|output| String::from_utf8_lossy(&output.stdout).to_string())
                    .map_err(Into::into)
            })
            .unwrap_or_else(|| Ok(String::from(">> ")))?;

        let readline = rl.readline(&prompt);
        match readline {
            Ok(line) => {
                let line = &line;
                let parsed: cow_ast::CommandStatement = match rsh::CommandStatementParser::new()
                    .parse(rt_ctx.shell_ctx, line, lexer::lexer(&line))
                {
                    Err(e) => {
                        println!("  Parse Error: {}", yansi::Paint::red(e.to_string()));
                        continue;
                    }
                    Ok(v) => match cow_ast::CommandStatement::from_ast(v, rt_ctx.shell_ctx) {
                        Err(e) => {
                            println!(
                                "  Interpolation Error: {}",
                                yansi::Paint::red(e.to_string())
                            );
                            continue;
                        }
                        Ok(v) => v,
                    },
                };
                match rt_ctx.run_cmd_stmt(parsed.owned(), None) {
                    Err(RuntimeError::Exit(v)) => return Ok(v),
                    Err(e) => println!("  Runtime Error: {}", yansi::Paint::red(e)),
                    Ok(_) => (),
                }
            }
            Err(ReadlineError::Interrupted) => (),
            Err(ReadlineError::Eof) => return Ok(0),
            Err(err) => Err(err)?,
        }
    }
}

enum AstFormat {
    Ron,
    Bincode,
}

impl FromStr for AstFormat {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_ascii_lowercase().as_str() {
            "ron" => Ok(Self::Ron),
            "bincode" => Ok(Self::Bincode),
            _ => Err("no such ast variant"),
        }
    }
}

#[derive(StructOpt)]
enum Builtin {
    Ast {
        code: String,
        #[structopt(short, long)]
        pretty: bool,
        #[structopt(short, long, default_value = "ron", possible_values = &["ron", "bincode"])]
        format: AstFormat,
    },
    RunAst {
        ast: String,
        #[structopt(short, long)]
        bincode: bool,
    },
}

impl Builtin {
    pub fn execute(self, shell_ctx: &mut ShellContext) -> ShResult<()> {
        match self {
            Builtin::Ast {
                code,
                pretty,
                format,
            } => {
                let code = &code;
                let parsed = rsh::CommandContextParser::new()
                    .parse(shell_ctx, code, lexer::lexer(&code))
                    .map_err(|err| Error::Parse(err.to_string()))?;
                match format {
                    AstFormat::Ron => println!(
                        "{}",
                        if pretty {
                            ron::ser::to_string_pretty(&parsed, Default::default())?
                        } else {
                            ron::to_string(&parsed)?
                        }
                    ),
                    AstFormat::Bincode => {
                        println!("{}", base64::encode(bincode::serialize(&parsed)?))
                    }
                }
            }
            Builtin::RunAst { ast, bincode } => {
                let data;
                let ast: cow_ast::CommandContext<'_> = if bincode {
                    data = base64::decode(ast)?;
                    bincode::deserialize(&data)?
                } else {
                    ron::from_str(&ast)?
                };
                let mut rt_ctx = RuntimeCtx::new(shell_ctx);
                rt_ctx.run_cmd_ctx(ast, None)?;
            }
        }

        Ok(())
    }

    pub fn is(name: &str) -> bool {
        match name {
            "ast" | "run-ast" => true,
            _ => false,
        }
    }
}

#[derive(StructOpt)]
struct Args {
    #[structopt(short, long)]
    command: Option<String>,
    #[structopt(subcommand)]
    sub_command: Option<SubCommands>,
    #[structopt(short, long)]
    prompt_command: Option<String>,
    file: Option<PathBuf>,
}

#[derive(StructOpt)]
enum SubCommands {
    Builtin(Builtin),
}

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;
    let args = Args::from_args();
    let mut shell_ctx = ShellContext::new();
    let cp = shell_ctx.current_process.clone();

    ctrlc::set_handler(move || {
        match cp.read().map_err(|e| e.into_inner()) {
            Err(e) | Ok(e) => {
                if let Some(child) = &*e {
                    // Don't really care if the kill did not work, you
                    // have bigger problems
                    let _ = child.kill();
                }
            }
        }
    })?;

    if let Some(subcommand) = args.sub_command {
        match subcommand {
            SubCommands::Builtin(builtin) => builtin.execute(&mut shell_ctx)?,
        }
    } else if let Some(command) = args.command {
        let command_parser = rsh::CommandContextParser::new();
        let command = &command;
        dbg!(report!(command_parser.parse(
            &mut shell_ctx,
            command,
            lexer::lexer(&command)
        )));
    } else if let Some(script) = args.file {
        let script = &std::fs::read_to_string(script)?;
        let parsed =
            report!(rsh::ScriptParser::new().parse(&mut shell_ctx, script, lexer::lexer(&script)));
        let mut rt_ctx = RuntimeCtx::new(&mut shell_ctx);
        let parsed = parsed
            .into_iter()
            .map(|s| cow_ast::Statement::from_ast(s, rt_ctx.shell_ctx))
            .collect::<Result<Vec<_>, _>>()?;
        match rt_ctx.run_script(&parsed) {
            Ok(_) => (),
            Err(RuntimeError::Exit(i)) => process::exit(i),
            Err(e) => {
                eprintln!("Error executing script: {}", e);
                process::exit(1);
            }
        }

        process::exit(0)
    } else {
        let exit = interactive_input(&mut shell_ctx, args.prompt_command.as_deref())?;
        process::exit(exit);
    }

    Ok(())
}
