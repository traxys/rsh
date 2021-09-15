#[macro_use]
extern crate lalrpop_util;
use builtin_functions::BuiltinFunction;
use lasso::{Rodeo, Spur};
use once_cell::sync::Lazy;
use regex::Regex;
use runtime::RuntimeCtx;
use rustyline::{error::ReadlineError, Editor};
use serde::{Deserialize, Serialize};
use shared_child::SharedChild;
use std::{
    path::PathBuf,
    process::{self, ExitStatus},
    str::FromStr,
    sync::{Arc, RwLock},
};
use structopt::StructOpt;

use crate::runtime::RuntimeError;

mod builtin_functions;
mod cowrc;
pub mod lexer;
pub mod runtime;
pub mod type_checker;

type ParseError<'input, T> =
    Result<T, lalrpop_util::ParseError<usize, lexer::Token<'input>, lexer::LexerError>>;

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
    TypeError { expected: Type, got: Type },
    #[error("runtime error: {0}")]
    RuntimeError(#[from] runtime::RuntimeError),
}

static INTERPOLATION_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"\$[a-zA-Z0-9_]+|\$\{[^{}]*\}").unwrap());

#[derive(Clone, Debug, Serialize, Deserialize)]
enum StringPart<'input> {
    Text(&'input str),
    Variable(Spur),
    Expression(Expression<'input>),
}

impl<'input> StringPart<'input> {
    pub fn interpolate(s: &'input str, ctx: &mut ShellContext) -> ParseError<'input, Vec<Self>> {
        let mut idx = 0;
        let mut interpolation = Vec::new();

        for mtch in INTERPOLATION_REGEX.find_iter(s) {
            if mtch.start() != idx {
                interpolation.push(Self::Text(&s[idx..mtch.start()]));
            }
            idx = mtch.end();
            let match_expr = &mtch.as_str()[1..];
            if match_expr.starts_with("{") {
                let input = match_expr.trim_start_matches('{').trim_end_matches('}');
                let expr =
                    rsh::StrongExpressionParser::new().parse(ctx, input, lexer::lexer(input))?;
                interpolation.push(Self::Expression(expr));
            } else {
                interpolation.push(Self::Variable(ctx.rodeo.get_or_intern(&mtch.as_str()[1..])));
            }
        }
        if idx < s.len() {
            interpolation.push(Self::Text(&s[idx..]))
        }

        Ok(interpolation)
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
enum RedirectionType {
    In,
    Out,
    Append,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Command<'input> {
    #[serde(borrow)]
    name: Expression<'input>,
    #[serde(borrow)]
    args: Vec<Expression<'input>>,
    #[serde(borrow)]
    redirections: Vec<(RedirectionType, Expression<'input>)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pipeline<'input> {
    #[serde(borrow)]
    commands: Vec<Command<'input>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ChainPart<'input> {
    #[serde(borrow)]
    Pipeline(Pipeline<'input>),
    #[serde(borrow)]
    Chain(Box<CommandChain<'input>>),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CommandChain<'input> {
    Or(ChainPart<'input>, Box<CommandChain<'input>>),
    And(ChainPart<'input>, Box<CommandChain<'input>>),
    #[serde(borrow)]
    Pipeline(Pipeline<'input>),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Type {
    Dynamic,
    Int,
    String,
    Bytes,
    Private,
    Function { ret: Box<Type>, args: Vec<Type> },
    List(Box<Type>),
    Iterator(Box<Type>),
    Option(Box<Type>),
}

enum TypeCheck {
    Compatible,
    Incompatible,
    Runtime,
}

impl Type {
    fn is_compatible(&self, expr_ty: &Type) -> TypeCheck {
        match (self, expr_ty) {
            (Self::Dynamic, _) => TypeCheck::Compatible,
            (_, Self::Dynamic) => TypeCheck::Runtime,
            (Self::Int, Self::Int) => TypeCheck::Compatible,
            (Self::String | Self::Bytes, Self::String | Self::Bytes) => TypeCheck::Compatible,
            (Self::Function { .. }, Self::Function { .. }) => TypeCheck::Compatible,
            _ => TypeCheck::Incompatible,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Dynamic => write!(f, "any"),
            Type::Int => write!(f, "int"),
            Type::String => write!(f, "str"),
            Type::Bytes => write!(f, "bytes"),
            Type::Private => write!(f, "<private>"),
            Type::Function { ret, args } => {
                write!(f, "fn(")?;
                if args.len() > 1 {
                    for arg in &args[0..args.len() - 2] {
                        write!(f, "{},", arg)?
                    }
                }
                if let Some(arg) = args.last() {
                    write!(f, "{}", arg)?
                }
                write!(f, ") -> {}", ret)
            }
            Type::List(inner) => write!(f, "[{}]", inner),
            Type::Iterator(item) => write!(f, "Iterator<{}>", item),
            Type::Option(item) => write!(f, "Option<{}>", item),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VariableDefinition<'input> {
    name: Spur,
    #[serde(borrow)]
    expr: Expression<'input>,
    ty: Type,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommandContext<'input> {
    #[serde(borrow)]
    commands: Vec<CommandChain<'input>>,
    #[serde(borrow)]
    variables: Vec<VariableDefinition<'input>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Statement<'input> {
    #[serde(borrow)]
    VarDef(VariableDefinition<'input>),
    #[serde(borrow)]
    Cmd(Vec<CommandContext<'input>>)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum Value<'input> {
    String(&'input str),
    Int(i64),
    List(Vec<Expression<'input>>),
}

impl<'input> Value<'input> {
    pub fn ty(&self) -> Type {
        match self {
            Value::String(_) => Type::String,
            Value::Int(_) => Type::Int,
            Value::List(_) => Type::List(Box::new(Type::Dynamic)),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum Expression<'input> {
    #[serde(borrow)]
    Value(Value<'input>),
    Call {
        function: Box<Expression<'input>>,
        args: Vec<Expression<'input>>,
    },
    Method {
        value: Box<Expression<'input>>,
        name: Spur,
        args: Vec<Expression<'input>>,
    },
    Interpolated(Vec<StringPart<'input>>),
    SubShell(Box<CommandContext<'input>>),
    Variable(Spur),
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
    let mut rl: Editor<()> = Editor::with_config(
        rustyline::Config::builder()
            .auto_add_history(true)
            .history_ignore_space(true)
            .tab_stop(4)
            .build(),
    );
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

    loop {
        let mut rt_ctx = runtime::RuntimeCtx::new(sh_ctx);

        let prompt = prompt_command
            .map(|command| -> color_eyre::Result<_> {
                let parsed = command_parser
                    .parse(rt_ctx.shell_ctx, command, lexer::lexer(command))
                    .map_err(|err| color_eyre::eyre::eyre!("could not parse prompt: {}", err))?;
                let mut cmd = rt_ctx.prepare_cmd(&parsed)?;
                cmd.output()
                    .map(|output| String::from_utf8_lossy(&output.stdout).to_string())
                    .map_err(Into::into)
            })
            .unwrap_or_else(|| Ok(String::from(">> ")))?;

        drop(rt_ctx);

        let readline = rl.readline(&prompt);
        match readline {
            Ok(line) => {
                let mut rt_ctx = runtime::RuntimeCtx::new(sh_ctx);
                let parsed = match rsh::CommandContextParser::new().parse(
                    rt_ctx.shell_ctx,
                    &line,
                    lexer::lexer(&line),
                ) {
                    Err(e) => {
                        println!("  Parse Error: {}", yansi::Paint::red(e.to_string()));
                        continue;
                    }
                    Ok(v) => v,
                };
                match rt_ctx.run_cmd_ctx(parsed) {
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
    pub fn execute(&self, shell_ctx: &mut ShellContext) -> ShResult<()> {
        match self {
            Builtin::Ast {
                code,
                pretty,
                format,
            } => {
                let parsed = rsh::CommandContextParser::new()
                    .parse(shell_ctx, code, lexer::lexer(code))
                    .map_err(|err| Error::Parse(err.to_string()))?;
                match format {
                    AstFormat::Ron => println!(
                        "{}",
                        if *pretty {
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
                let ast: CommandContext<'_> = if *bincode {
                    data = base64::decode(ast)?;
                    bincode::deserialize(&data)?
                } else {
                    ron::from_str(ast)?
                };
                let mut rt_ctx = RuntimeCtx::new(shell_ctx);
                rt_ctx.run_cmd_ctx(ast)?;
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

    if let Some(subcommand) = &args.sub_command {
        match subcommand {
            SubCommands::Builtin(builtin) => builtin.execute(&mut shell_ctx)?,
        }
    } else if let Some(command) = &args.command {
        let command_parser = rsh::CommandContextParser::new();
        dbg!(report!(command_parser.parse(
            &mut shell_ctx,
            &command,
            lexer::lexer(&command)
        )));
    } else if let Some(script) = args.file {
        let script = std::fs::read_to_string(script)?;
        let parsed =
            report!(rsh::ScriptParser::new().parse(&mut shell_ctx, &script, lexer::lexer(&script)));
        let mut rt_ctx = RuntimeCtx::new(&mut shell_ctx);
        for stmt in parsed {
            match rt_ctx.run_statement(stmt) {
                Ok(_) => (),
                Err(RuntimeError::Exit(i)) => process::exit(i),
                Err(e) => {
                    eprintln!("Error executing script: {}", e);
                    process::exit(1);
                }
            }
        }

        process::exit(0)
    } else {
        let exit = interactive_input(&mut shell_ctx, args.prompt_command.as_deref())?;
        process::exit(exit);
    }

    Ok(())
}
