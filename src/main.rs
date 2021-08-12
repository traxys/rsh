#[macro_use]
extern crate lalrpop_util;
use rustyline::{error::ReadlineError, Editor};
use shared_child::SharedChild;
use std::{
    borrow::Cow,
    collections::HashMap,
    process::{self, ExitStatus, Stdio},
    sync::{Arc, RwLock},
};
use structopt::StructOpt;

lalrpop_mod!(pub rsh);

type ShResult<T, E = Error> = std::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

#[derive(Clone, Copy, Debug)]
pub enum StringValue<'input> {
    Litteral(&'input str),
    Variable(&'input str),
}

impl<'input> StringValue<'input> {
    pub fn resolve(&self, context: &ExecutionContext<'input>) -> Cow<'input, str> {
        match self {
            Self::Litteral(l) => Cow::from(*l),
            Self::Variable(name) => context
                .variables
                .get(name)
                .map(|v| v.stringy(context))
                .flatten()
                .unwrap_or_else(|| {
                    println!("Warning: {} was not defined", name);
                    Cow::from("")
                }),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Command<'input> {
    name: StringValue<'input>,
    args: Vec<StringValue<'input>>,
}

impl<'input> Command<'input> {
    pub fn prepare(&self, context: &ExecutionContext<'input>) -> process::Command {
        let mut command = process::Command::new(self.name.resolve(context).as_ref());
        let args: Vec<_> = self.args.iter().map(|v| v.resolve(context)).collect();
        command.args(args.iter().map(|v| v.as_ref()));
        command
    }
}

#[derive(Clone, Debug)]
pub struct Pipeline<'input> {
    commands: Vec<Command<'input>>,
}

impl<'input> Pipeline<'input> {
    pub fn execute(&self, context: &ExecutionContext<'input>) -> ShResult<ExitStatus> {
        let mut prepared: Vec<_> = self.commands.iter().map(|c| c.prepare(context)).collect();
        //let mut children = Vec::new();
        if prepared.len() == 1 {
            let command = SharedChild::spawn(&mut prepared[0])?;
            *context.shell_ctx.current_process.write().unwrap() = Some(command);
            context
                .shell_ctx
                .current_process
                .read()
                .unwrap()
                .as_ref()
                .unwrap()
                .wait()
                .map_err(Into::into)
        } else {
            let mut children = vec![prepared[0].stdout(Stdio::piped()).spawn()?];
            let len = prepared.len();
            if len > 2 {
                for command in &mut prepared[1..len - 1] {
                    let com = command
                        .stdin(children.last_mut().unwrap().stdout.take().unwrap())
                        .stdout(Stdio::piped())
                        .spawn()?;
                    children.push(com)
                }
            }

            let res = prepared
                .last_mut()
                .unwrap()
                .stdin(children.last_mut().unwrap().stdout.take().unwrap())
                .status()
                .map_err(Into::into);

            children.iter_mut().for_each(|p| {
                let _ = p.kill();
            });

            res
        }
    }
}

#[derive(Clone, Debug)]
pub enum ChainPart<'input> {
    Pipeline(Pipeline<'input>),
    Chain(Box<CommandChain<'input>>),
}

impl<'input> ChainPart<'input> {
    pub fn execute(&self, context: &ExecutionContext<'input>) -> ShResult<ExitStatus> {
        match self {
            ChainPart::Pipeline(p) => p.execute(context),
            ChainPart::Chain(c) => c.execute(context),
        }
    }
}

#[derive(Clone, Debug)]
pub enum CommandChain<'input> {
    Or(ChainPart<'input>, Box<CommandChain<'input>>),
    And(ChainPart<'input>, Box<CommandChain<'input>>),
    Pipeline(Pipeline<'input>),
}

impl<'input> CommandChain<'input> {
    pub fn execute(&self, context: &ExecutionContext) -> ShResult<ExitStatus> {
        match self {
            CommandChain::Or(c, rest) => {
                let result = c.execute(context)?;
                if result.success() {
                    Ok(result)
                } else {
                    rest.execute(context)
                }
            }
            CommandChain::And(c, rest) => {
                let result = c.execute(context)?;
                if result.success() {
                    rest.execute(context)
                } else {
                    Ok(result)
                }
            }
            CommandChain::Pipeline(p) => p.execute(context),
        }
    }
}

#[derive(Clone, Debug)]
pub struct VariableDefinition<'input> {
    name: &'input str,
    value: StringValue<'input>,
}

#[derive(Clone, Debug)]
pub struct CommandContext<'input> {
    commands: Vec<CommandChain<'input>>,
    variables: Vec<VariableDefinition<'input>>,
}

impl<'input> CommandContext<'input> {
    fn define_context(&self, shell_ctx: &'input mut ShellContext) -> ExecutionContext<'input> {
        ExecutionContext {
            variables: self
                .variables
                .iter()
                .map(|def| (def.name, Value::String(def.value)))
                .collect(),
            shell_ctx,
        }
    }

    fn execute(&self, sh_ctx: &'input mut ShellContext) -> ShResult<()> {
        let context = self.define_context(sh_ctx);
        for command in &self.commands {
            command.execute(&context)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum Value<'input> {
    String(StringValue<'input>),
}

impl<'input> Value<'input> {
    pub fn stringy(&self, context: &ExecutionContext<'input>) -> Option<Cow<'input, str>> {
        match self {
            Value::String(s) => Some(s.resolve(context)),
        }
    }
}

pub struct ExecutionContext<'input> {
    variables: HashMap<&'input str, Value<'input>>,
    shell_ctx: &'input mut ShellContext,
}

pub struct ShellContext {
    current_process: Arc<RwLock<Option<SharedChild>>>,
}

impl ShellContext {
    pub fn new() -> Self {
        ShellContext {
            current_process: Arc::new(RwLock::new(None)),
        }
    }
}

#[derive(StructOpt)]
struct Args {
    #[structopt(short, long)]
    command: Option<String>,
}

macro_rules! report {
    ($e:expr) => {
        match $e {
            Err(e) => color_eyre::eyre::bail!("An error occured: {}", e),
            Ok(v) => v,
        }
    };
}

fn interactive_input(sh_ctx: &mut ShellContext) -> color_eyre::Result<()> {
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
    let res = interactive_loop(&mut rl, sh_ctx);
    rl.save_history("/home/traxys/.rsh-history")?;
    res
}

fn interactive_loop<E: rustyline::Helper>(
    rl: &mut rustyline::Editor<E>,
    sh_ctx: &mut ShellContext,
) -> color_eyre::Result<()> {
    loop {
        let readline = rl.readline(">> ");
        match readline {
            Ok(line) => {
                let parsed = match rsh::CommandContextParser::new().parse(&line) {
                    Err(e) => {
                        println!("  Parse Error: {}", yansi::Paint::red(e.to_string()));
                        continue;
                    }
                    Ok(v) => v,
                };
                if let Err(e) = parsed.execute(sh_ctx) {
                    println!("  Execution Error: {}", yansi::Paint::red(e))
                }
            }
            Err(ReadlineError::Interrupted) => println!("Interrupted"),
            Err(ReadlineError::Eof) => return Ok(()),
            Err(err) => Err(err)?,
        }
    }
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

    if let Some(command) = &args.command {
        let command_parser = rsh::CommandContextParser::new();
        dbg!(report!(command_parser.parse(&command)));
    } else {
        interactive_input(&mut shell_ctx)?;
    }

    Ok(())
}
