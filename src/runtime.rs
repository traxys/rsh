use crate::{
    type_checker::{TypeCheckerCtx, TypeError},
    Builtin, RedirectionType, ShellContext, Type,
};
use lasso::Spur;
use shared_child::SharedChild;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fs::{File, OpenOptions},
    process::{self, ExitStatus, Stdio},
    rc::Rc,
};

pub type RuntimeResult<T> = Result<T, RuntimeError>;

#[derive(Debug, thiserror::Error)]
pub enum RuntimeError {
    #[error("exit {0}")]
    Exit(i32),
    #[error("i/o error")]
    Io(#[from] std::io::Error),
    #[error("ser/de error")]
    SerDe(#[from] ron::Error),
    #[error("cycle in evaluation: {:?}", _0)]
    EvaluationCycle(Vec<String>),
    #[error("undefined: {}", _0)]
    Undefined(String),
    #[error("static errors: {:?}", _0)]
    Static(Vec<TypeError>),
    #[error("type {} is not callable", _0)]
    UncallableType(Type),
    #[error("unexpected type: expected {}, got {}", expected, got)]
    UnexpctedType { expected: Type, got: Type },
    #[error("unexpected argument count: expected {}, got {}", expected, got)]
    InvalidArgCount { expected: usize, got: usize },
}

#[derive(Debug)]
enum Value<'input> {
    Str(Cow<'input, str>),
    Int(i64),
    Bytes(Vec<u8>),
    NativeFn(usize),
}

const NATIVE_FNS: &[&'static str] = &["s"];

impl<'input> Value<'input> {
    pub fn to_string(&self) -> Cow<'input, str> {
        match self {
            Value::Str(v) => v.clone(),
            Value::Int(i) => Cow::Owned(i.to_string()),
            Value::Bytes(v) => String::from_utf8_lossy(v).to_string().into(),
            Value::NativeFn(id) => format!("<native fn {}>", NATIVE_FNS[*id],).into(),
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Value::Str(_) => Type::String,
            Value::Int(_) => Type::Int,
            Value::Bytes(_) => Type::Bytes,
            Value::NativeFn(_id) => todo!(),
        }
    }
}

pub struct RuntimeCtx<'input> {
    pub shell_ctx: &'input mut ShellContext,
    overlays: Vec<Overlay<'input>>,
    exit: Spur,
}

#[derive(Debug)]
pub struct Overlay<'input> {
    definitions: HashMap<Spur, super::Expression<'input>>,
    values: HashMap<Spur, Rc<Value<'input>>>,
    currently_evaluating: HashSet<Spur>,
}

fn root_overlay<'input>(sh_ctx: &mut ShellContext) -> Overlay<'input> {
    let mut values = HashMap::new();
    for (id, name) in NATIVE_FNS.iter().enumerate() {
        values.insert(
            sh_ctx.rodeo.get_or_intern_static(name),
            Rc::new(Value::NativeFn(id)),
        );
    }
    Overlay {
        definitions: HashMap::new(),
        values,
        currently_evaluating: HashSet::new(),
    }
}

impl<'input> RuntimeCtx<'input> {
    pub fn new(shell_ctx: &'input mut ShellContext) -> Self {
        Self {
            exit: shell_ctx.rodeo.get_or_intern_static("exit"),
            overlays: vec![root_overlay(shell_ctx)],
            shell_ctx,
        }
    }

    fn enter_overlay(&mut self, definitions: Vec<super::VariableDefinition<'input>>) {
        let overlay = Overlay {
            values: HashMap::new(),
            definitions: definitions
                .iter()
                .map(|def| (def.name, def.expr.clone()))
                .collect(),
            currently_evaluating: HashSet::new(),
        };
        self.overlays.push(overlay);
    }

    pub(crate) fn prepare_cmd(
        &mut self,
        command: &super::Command<'input>,
    ) -> RuntimeResult<process::Command> {
        let name = self.eval_expr(&command.name)?.to_string();
        if name == "exit" {
            if command.args.len() > 1 {
                return Err(RuntimeError::Exit(255));
            }

            match command
                .args
                .first()
                .map(|v| self.eval_expr(v).map(|v| v.to_string().parse()))
            {
                Some(Ok(Ok(e))) => return Err(RuntimeError::Exit(e)),
                Some(Err(e)) => return Err(e),
                _ => return Err(RuntimeError::Exit(255)),
            }
        }

        let mut cmd;
        if Builtin::is(&name) {
            cmd = process::Command::new(std::env::current_exe()?);
            cmd.arg("builtin").arg(&*name);
        } else {
            cmd = process::Command::new(&*name);
        }

        let args: Vec<_> = command
            .args
            .iter()
            .map(|v| self.eval_expr(v).map(|v| v.to_string()))
            .collect::<RuntimeResult<_>>()?;
        cmd.args(args.iter().map(|x| x.as_ref()));

        for (ty, path) in &command.redirections {
            let path = self.eval_expr(&path)?.to_string();
            match ty {
                RedirectionType::In => {
                    let file = File::open(&*path)?;
                    cmd.stdin(file);
                }
                RedirectionType::Out => {
                    let file = OpenOptions::new().create(true).write(true).open(&*path)?;
                    cmd.stdout(file);
                }
                RedirectionType::Append => {
                    let file = OpenOptions::new().create(true).append(true).open(&*path)?;
                    cmd.stdout(file);
                }
            }
        }
        Ok(cmd)
    }

    fn prepare_pipeline(
        &mut self,
        pipeline: &super::Pipeline<'input>,
    ) -> RuntimeResult<(Vec<process::Child>, process::Command)> {
        let mut prepared: Vec<_> = pipeline
            .commands
            .iter()
            .map(|c| self.prepare_cmd(c))
            .collect::<RuntimeResult<_>>()?;
        if prepared.len() == 1 {
            return Ok((vec![], prepared.pop().unwrap()));
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
            let mut last = prepared.pop().unwrap();
            last.stdin(children.last_mut().unwrap().stdout.take().unwrap());

            Ok((children, last))
        }
    }

    fn run_pipeline(&mut self, pipeline: &super::Pipeline<'input>) -> RuntimeResult<ExitStatus> {
        let (mut children, mut last) = self.prepare_pipeline(pipeline)?;
        let command = SharedChild::spawn(&mut last)?;
        *self.shell_ctx.current_process.write().unwrap() = Some(command);
        let res = self
            .shell_ctx
            .current_process
            .read()
            .unwrap()
            .as_ref()
            .unwrap()
            .wait()
            .map_err(Into::into);

        children.iter_mut().for_each(|p| {
            let _ = p.kill();
        });

        res
    }

    fn run_chain_part(
        &mut self,
        chain_part: &super::ChainPart<'input>,
    ) -> RuntimeResult<ExitStatus> {
        match chain_part {
            super::ChainPart::Pipeline(p) => self.run_pipeline(p),
            super::ChainPart::Chain(c) => self.run_chain(c),
        }
    }

    fn run_chain(&mut self, chain: &super::CommandChain<'input>) -> RuntimeResult<ExitStatus> {
        match chain {
            super::CommandChain::Or(c, rest) => {
                let result = self.run_chain_part(c)?;
                if result.success() {
                    Ok(result)
                } else {
                    self.run_chain(rest)
                }
            }
            super::CommandChain::And(c, rest) => {
                let result = self.run_chain_part(c)?;
                if result.success() {
                    self.run_chain(rest)
                } else {
                    Ok(result)
                }
            }
            super::CommandChain::Pipeline(p) => self.run_pipeline(p),
        }
    }

    pub fn run_cmd_ctx(&mut self, cmd_ctx: super::CommandContext<'input>) -> RuntimeResult<()> {
        TypeCheckerCtx::new(self.shell_ctx)
            .check_cmd_ctx(&cmd_ctx)
            .map_err(|ty_errs| RuntimeError::Static(ty_errs))?;

        self.enter_overlay(cmd_ctx.variables);

        for command in &cmd_ctx.commands {
            self.shell_ctx.last_exit = Some(self.run_chain(command)?);
        }

        self.overlays.pop();

        Ok(())
    }

    fn run_interpolation(
        &mut self,
        fstring: &[super::StringPart<'input>],
    ) -> RuntimeResult<Cow<'input, str>> {
        match fstring {
            [super::StringPart::Text(v)] => Ok(Cow::from(*v)),
            [super::StringPart::Variable(v)] => self.resolve_text(*v),
            _ => fstring
                .iter()
                .try_fold(String::new(), |mut current, segment| -> RuntimeResult<_> {
                    match segment {
                        super::StringPart::Text(s) => current.push_str(s),
                        super::StringPart::Variable(v) => current.push_str(&self.resolve_text(*v)?),
                    }
                    Ok(current)
                })
                .map(Cow::from),
        }
    }

    fn resolve_text(&mut self, name: Spur) -> RuntimeResult<Cow<'input, str>> {
        match self.resolve(name)? {
            None => {
                eprintln!(
                    "Warning: {} was not defined",
                    self.shell_ctx
                        .rodeo
                        .try_resolve(&name)
                        .unwrap_or("<unknown>")
                );
                Ok(Cow::Borrowed(""))
            }
            Some(v) => Ok(v.to_string()),
        }
    }

    fn rec_resolve(&mut self, name: Spur) -> RuntimeResult<Option<Rc<Value<'input>>>> {
        for idx in (0..self.overlays.len()).rev() {
            let overlay = &mut self.overlays[idx];
            let expr = match overlay.values.get(&name) {
                None => match overlay.definitions.get(&name) {
                    None => {
                        continue;
                    }
                    Some(expr) => expr.clone(),
                },
                Some(v) => return Ok(Some(v.clone())),
            };

            if !overlay.currently_evaluating.insert(name) {
                return Err(RuntimeError::EvaluationCycle(
                    overlay
                        .currently_evaluating
                        .clone()
                        .iter()
                        .map(|spur| {
                            self.shell_ctx
                                .rodeo
                                .try_resolve(spur)
                                .unwrap_or("<unknown>")
                                .to_owned()
                        })
                        .collect(),
                ));
            };
            let val = self.eval_expr(&expr)?;
            let overlay = &mut self.overlays[idx];
            overlay.currently_evaluating.remove(&name);
            overlay.values.insert(name, val.clone());
            return Ok(Some(val));
        }

        // TODO: Env Var
        Ok(None)
    }

    fn resolve(&mut self, name: Spur) -> RuntimeResult<Option<Rc<Value<'input>>>> {
        if name == self.exit {
            Ok(Some(Rc::new(Value::Int(
                self.shell_ctx
                    .last_exit
                    .map(|v| v.code())
                    .flatten()
                    .unwrap_or(0) as i64,
            ))))
        } else {
            self.rec_resolve(name)
        }
    }

    fn call_native_function(
        &mut self,
        id: usize,
        args: Vec<Rc<Value<'input>>>,
    ) -> RuntimeResult<Rc<Value<'input>>> {
        fn check_args<'input>(expected: usize, args: &[Rc<Value<'input>>]) -> RuntimeResult<()> {
            if args.len() != expected {
                Err(RuntimeError::InvalidArgCount {
                    expected,
                    got: args.len(),
                })
            } else {
                Ok(())
            }
        }

        match id {
            // s
            0 => {
                check_args(1, &args)?;
                Ok(Rc::new(Value::Str(args[0].to_string())))
            }
            _ => unreachable!("invalid native function got called ({})", id),
        }
    }

    fn call_function(
        &mut self,
        function: Rc<Value<'input>>,
        args: Vec<Rc<Value<'input>>>,
    ) -> RuntimeResult<Rc<Value<'input>>> {
        match &*function {
            Value::NativeFn(id) => self.call_native_function(*id, args),
            val => return Err(RuntimeError::UncallableType(val.ty())),
        }
    }

    fn eval_expr(&mut self, expr: &super::Expression<'input>) -> RuntimeResult<Rc<Value<'input>>> {
        match expr {
            super::Expression::SubShell(code) => Ok(Rc::new(Value::Bytes(
                process::Command::new(std::env::current_exe()?)
                    .arg("builtin")
                    .arg("run-ast")
                    .arg(ron::to_string(code)?)
                    .output()?
                    .stdout,
            ))),
            super::Expression::Value(v) => match v {
                super::Value::String(s) => Ok(Rc::new(Value::Str(Cow::from(*s)))),
                super::Value::Int(i) => Ok(Rc::new(Value::Int(*i))),
            },
            super::Expression::Call { function, args } => {
                let function = self.eval_expr(function)?;
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.eval_expr(arg))
                    .collect::<RuntimeResult<_>>()?;
                self.call_function(function, args)
            }
            super::Expression::Interpolated(i) => {
                self.run_interpolation(i).map(Value::Str).map(Rc::new)
            }
            super::Expression::Variable(v) => self.resolve(*v)?.map(Ok).unwrap_or_else(|| {
                Err(RuntimeError::Undefined(
                    self.shell_ctx
                        .rodeo
                        .try_resolve(v)
                        .unwrap_or("<unkown>")
                        .to_owned(),
                ))
            }),
        }
    }
}
