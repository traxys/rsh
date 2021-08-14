#[macro_use]
extern crate lalrpop_util;
use bstr::{BStr, BString, ByteSlice, ByteVec};
use once_cell::sync::Lazy;
use regex::Regex;
use rustyline::{error::ReadlineError, Editor};
use serde::{Deserialize, Serialize};
use shared_child::SharedChild;
use std::{
    borrow::Cow,
    collections::HashMap,
    fs::{File, OpenOptions},
    process::{self, ExitStatus, Stdio},
    sync::{Arc, RwLock},
};
use structopt::StructOpt;

lalrpop_mod!(pub rsh);
lalrpop_mod!(pub fstring);

type ShResult<T, E = Error> = std::result::Result<T, E>;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("ser/de error: {0}")]
    Serde(#[from] ron::Error),
    #[error("called exit: {0}")]
    Exited(i32),
    #[error("parse error: {0}")]
    Parse(String),
    #[error("type error: expected {expected} got {got}")]
    TypeError { expected: Type, got: Type },
}

static VARIABLE_REGEX: Lazy<Regex> = Lazy::new(|| Regex::new(r"\$[a-zA-Z0-9_]+").unwrap());

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StringPart<'input> {
    Text(&'input str),
    Variable(&'input str),
}

impl<'input> StringPart<'input> {
    pub fn interpolate(s: &'input str) -> Vec<Self> {
        let mut idx = 0;
        let mut interpolation = Vec::new();

        for mtch in VARIABLE_REGEX.find_iter(s) {
            if mtch.start() != idx {
                interpolation.push(Self::Text(&s[idx..mtch.start()]));
            }
            idx = mtch.end();
            interpolation.push(Self::Variable(&mtch.as_str()[1..]));
        }
        if idx < s.len() {
            interpolation.push(Self::Text(&s[idx..]))
        }

        interpolation
    }

    pub fn resolve(
        fstring: &[StringPart<'input>],
        context: &ExecutionContext<'input>,
    ) -> Cow<'input, BStr> {
        match fstring {
            [Self::Text(v)] => v.as_bytes().as_bstr().into(),
            [Self::Variable(v)] => context.resolve_text(v),
            _ => fstring
                .iter()
                .fold(BString::from(Vec::new()), |mut current, segment| {
                    match segment {
                        StringPart::Text(s) => current.extend_from_slice(s.as_bytes()),
                        StringPart::Variable(v) => {
                            current.extend_from_slice(&context.resolve_text(v))
                        }
                    }
                    current
                })
                .into(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StringValue<'input> {
    Litteral(&'input str),
    // Variable(&'input str),
    Interpolated(Vec<StringPart<'input>>),
    SubShell(Box<CommandContext<'input>>),
    Env(BString),
}

impl<'input> StringValue<'input> {
    pub fn resolve(&self, context: &ExecutionContext<'input>) -> Cow<'input, BStr> {
        match self {
            Self::Litteral(l) => Cow::from(l.as_bytes().as_bstr()),
            // Self::Variable(name) => context.resolve_text(name),
            Self::SubShell(s) => sub_shell_exec(s, context)
                .map(Cow::from)
                .map_err(|e| {
                    eprintln!("Warning: subshell failed: {}", e);
                })
                .unwrap_or(Cow::from(b"".as_bstr())),
            StringValue::Interpolated(f) => StringPart::resolve(f, context).into(),
            Self::Env(e) => Cow::Owned(e.clone()),
        }
    }
}

fn sub_shell_exec<'input>(
    code: &CommandContext<'input>,
    // TODO: carry context
    _context: &ExecutionContext<'input>,
) -> ShResult<BString> {
    Ok(BString::from(
        process::Command::new(std::env::current_exe()?)
            .arg("builtin")
            .arg("run-ast")
            .arg(ron::to_string(code)?)
            .output()?
            .stdout,
    ))
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
    name: StringValue<'input>,
    #[serde(borrow)]
    args: Vec<Value<'input>>,
    #[serde(borrow)]
    redirections: Vec<(RedirectionType, Value<'input>)>,
}

impl<'input> Command<'input> {
    pub fn prepare(&self, context: &ExecutionContext<'input>) -> ShResult<process::Command> {
        let name = self.name.resolve(context);
        if name == b"exit".as_bstr() {
            if self.args.len() > 1 {
                return Err(Error::Exited(255));
            }
            match self
                .args
                .first()
                .map(|v| v.stringy(context).to_str().map(|s| s.parse()))
            {
                Some(Ok(Ok(v))) => return Err(Error::Exited(v)),
                _ => return Err(Error::Exited(255)),
            }
        }

        let mut command;
        if Builtin::is(&name) {
            command = process::Command::new(std::env::current_exe()?);
            command.arg("builtin").arg(name.to_os_str_lossy());
        } else {
            command = process::Command::new(name.to_os_str_lossy());
        }
        let args: Vec<_> = self.args.iter().map(|v| v.stringy(context)).collect();
        command.args(args.iter().map(|v| v.to_os_str_lossy()));
        for (ty, path) in &self.redirections {
            let path = path.stringy(context);
            let path = path.to_path_lossy();
            match ty {
                RedirectionType::In => {
                    let file = File::open(path)?;
                    command.stdin(file);
                }
                RedirectionType::Out => {
                    let file = OpenOptions::new().create(true).write(true).open(path)?;
                    command.stdout(file);
                }
                RedirectionType::Append => {
                    let file = OpenOptions::new().create(true).append(true).open(path)?;
                    command.stdout(file);
                }
            }
        }
        Ok(command)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pipeline<'input> {
    #[serde(borrow)]
    commands: Vec<Command<'input>>,
}

impl<'input> Pipeline<'input> {
    pub fn execute(&self, context: &ExecutionContext<'input>) -> ShResult<ExitStatus> {
        let mut prepared: Vec<_> = self
            .commands
            .iter()
            .map(|c| c.prepare(context))
            .collect::<ShResult<_>>()?;

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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ChainPart<'input> {
    #[serde(borrow)]
    Pipeline(Pipeline<'input>),
    #[serde(borrow)]
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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CommandChain<'input> {
    Or(ChainPart<'input>, Box<CommandChain<'input>>),
    And(ChainPart<'input>, Box<CommandChain<'input>>),
    #[serde(borrow)]
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

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub enum Type {
    Dynamic,
    Int,
    String,
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Dynamic => write!(f, "any"),
            Type::Int => write!(f, "int"),
            Type::String => write!(f, "str"),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VariableDefinition<'input> {
    name: &'input str,
    value: Value<'input>,
    ty: Type,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommandContext<'input> {
    #[serde(borrow)]
    commands: Vec<CommandChain<'input>>,
    #[serde(borrow)]
    variables: Vec<VariableDefinition<'input>>,
}

impl<'input> CommandContext<'input> {
    fn define_context(
        &self,
        shell_ctx: &'input mut ShellContext,
    ) -> ShResult<ExecutionContext<'input>> {
        Ok(ExecutionContext {
            variables: self
                .variables
                .iter()
                .map(|def| {
                    if !def.value.typechecks(def.ty) {
                        Err(Error::TypeError {
                            expected: def.ty,
                            got: def.value.ty(),
                        })
                    } else {
                        Ok((def.name, def.value.clone()))
                    }
                })
                .collect::<ShResult<_>>()?,
            shell_ctx,
        })
    }

    fn execute(&self, sh_ctx: &'input mut ShellContext) -> ShResult<()> {
        let context = self.define_context(sh_ctx)?;
        for command in &self.commands {
            context.shell_ctx.last_exit = Some(command.execute(&context)?);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum Value<'input> {
    #[serde(borrow)]
    String(StringValue<'input>),
    Int(i64),
}

impl<'input> Value<'input> {
    pub fn stringy(&self, context: &ExecutionContext<'input>) -> Cow<'input, BStr> {
        match self {
            Value::String(s) => s.resolve(context),
            Value::Int(i) => Cow::from(BString::from(i.to_string().into_bytes())),
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Value::String(_) => Type::String,
            Value::Int(_) => Type::Int,
        }
    }

    fn typechecks(&self, ty: Type) -> bool {
        match ty {
            Type::Dynamic => true,
            Type::Int => match self.ty() {
                Type::Int => true,
                _ => false,
            },
            Type::String => match self.ty() {
                Type::String => true,
                _ => false,
            },
        }
    }
}

pub struct ExecutionContext<'input> {
    variables: HashMap<&'input str, Value<'input>>,
    shell_ctx: &'input mut ShellContext,
}

impl<'input> ExecutionContext<'input> {
    fn resolve(&self, name: &'input str) -> Option<Cow<'_, Value<'input>>> {
        match name {
            "exit" => self
                .shell_ctx
                .last_exit
                .map(|v| v.code())
                .flatten()
                .map(|v| Cow::Owned(Value::Int(v as i64))),
            _ => self
                .variables
                .get(name)
                .map(|var| Cow::Borrowed(var))
                .or_else(|| {
                    std::env::var_os(name).map(|v| {
                        Cow::Owned(Value::String(StringValue::Env(
                            Vec::from_os_string(v)
                                .map(|v| BString::from(v))
                                .unwrap_or_else(|_| {
                                    eprintln!("Warning: could not read env var {}", name);
                                    BString::from(Vec::new())
                                }),
                        )))
                    })
                }),
        }
    }

    fn resolve_text(&self, name: &'input str) -> Cow<'input, BStr> {
        self.resolve(name)
            .map(|val| val.stringy(self))
            .unwrap_or_else(|| {
                if name != "exit" {
                    eprintln!("Warning: {} was not defined", name);
                }
                Cow::Borrowed(b"".as_bstr())
            })
    }
}

pub struct ShellContext {
    current_process: Arc<RwLock<Option<SharedChild>>>,
    last_exit: Option<ExitStatus>,
}

impl ShellContext {
    pub fn new() -> Self {
        ShellContext {
            current_process: Arc::new(RwLock::new(None)),
            last_exit: None,
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
        let prompt = prompt_command
            .map(|command| -> color_eyre::Result<_> {
                let parsed = command_parser
                    .parse(command)
                    .map_err(|err| color_eyre::eyre::eyre!("could not parse prompt: {}", err))?;
                let mut cmd = parsed.prepare(&ExecutionContext {
                    variables: HashMap::new(),
                    shell_ctx: sh_ctx,
                })?;
                cmd.output()
                    .map(|output| String::from_utf8_lossy(&output.stdout).to_string())
                    .map_err(Into::into)
            })
            .unwrap_or_else(|| Ok(String::from(">> ")))?;

        let readline = rl.readline(&prompt);
        match readline {
            Ok(line) => {
                let parsed = match rsh::CommandContextParser::new().parse(&line) {
                    Err(e) => {
                        println!("  Parse Error: {}", yansi::Paint::red(e.to_string()));
                        continue;
                    }
                    Ok(v) => v,
                };
                match parsed.execute(sh_ctx) {
                    Err(Error::Exited(v)) => return Ok(v),
                    Err(e) => println!("  Execution Error: {}", yansi::Paint::red(e)),
                    Ok(_) => (),
                }
            }
            Err(ReadlineError::Interrupted) => println!("Interrupted"),
            Err(ReadlineError::Eof) => return Ok(0),
            Err(err) => Err(err)?,
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
}

#[derive(StructOpt)]
enum SubCommands {
    Builtin(Builtin),
}

#[derive(StructOpt)]
enum Builtin {
    Ast { code: String },
    RunAst { ast: String },
}

impl Builtin {
    pub fn execute(&self, shell_ctx: &mut ShellContext) -> ShResult<()> {
        match self {
            Builtin::Ast { code } => {
                let parsed = rsh::CommandContextParser::new()
                    .parse(code)
                    .map_err(|err| Error::Parse(err.to_string()))?;
                println!("{}", ron::to_string(&parsed)?);
            }
            Builtin::RunAst { ast } => {
                let ast: CommandContext<'_> = ron::from_str(ast)?;
                ast.execute(shell_ctx)?;
            }
        }

        Ok(())
    }

    pub fn is(name: &[u8]) -> bool {
        match name {
            b"ast" | b"run-ast" => true,
            _ => false,
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

    if let Some(subcommand) = &args.sub_command {
        match subcommand {
            SubCommands::Builtin(builtin) => builtin.execute(&mut shell_ctx)?,
        }
    } else if let Some(command) = &args.command {
        let command_parser = rsh::CommandContextParser::new();
        dbg!(report!(command_parser.parse(&command)));
    } else {
        let exit = interactive_input(&mut shell_ctx, args.prompt_command.as_deref())?;
        process::exit(exit);
    }

    Ok(())
}
