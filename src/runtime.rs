use crate::{
    cow_ast::{self, RedirectionType, Statement, Type},
    type_checker::{TypeCheckerCtx, TypeError},
    Builtin, ShellContext,
};
use gc::{Finalize, Gc, GcCell, Trace};
use lasso::Spur;
use serde::{ser::SerializeSeq, Serialize};
use shared_child::SharedChild;
use std::{
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
    #[error("i/o error: {0}")]
    Io(#[from] std::io::Error),
    #[error("ser/de error: {0}")]
    SerDe(#[from] bincode::Error),
    #[error("json ser/de error: {0}")]
    JsonSerDe(#[from] serde_json::Error),
    #[error("cycle in evaluation: {:?}", _0)]
    EvaluationCycle(Vec<String>),
    #[error("undefined: {}", _0)]
    Undefined(String),
    #[error("static errors: {:?}", _0)]
    Static(Vec<TypeError>),
    #[error("type {} is not callable", _0)]
    UncallableType(Type),
    #[error("unexpected type: expected {}, got {}", expected, got)]
    UnexpectedType { expected: Type, got: Type },
    #[error("unexpected argument count: expected {}, got {}", expected, got)]
    InvalidArgCount { expected: usize, got: usize },
    #[error("unexpected error: {}", _0)]
    UnexpectedError(String),
}

#[derive(Debug, Clone, Trace, Finalize)]
// TODO: optimize such that we don't need to box everything like numbers for example
enum Value {
    Str(Rc<String>),
    Int(i64),
    Bytes(Rc<Vec<u8>>),
    Function(FunctionValue),
    List(Gc<Vec<GcCell<Value>>>),
    Iterator(IteratorValue),
    Option(Option<Gc<Value>>),
    Private(PrivateValue),
}

#[derive(Debug, Clone, Trace, Finalize)]
struct IteratorValue {
    value: Gc<GcCell<Value>>,
    next: FunctionValue,
}

#[derive(Clone, Debug, Trace, Finalize)]
enum PrivateValue {
    Range { start: i64, end: i64 },
}

#[derive(Debug, Clone, Trace, Finalize)]
enum FunctionValue {
    NativeFn(isize),
}

impl FunctionValue {
    fn to_string(&self) -> String {
        match self {
            FunctionValue::NativeFn(id) => format!("<native fn {}>", id),
        }
    }
}

impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Value::Str(s) => serializer.serialize_str(s),
            Value::Int(i) => serializer.serialize_i64(*i),
            Value::Bytes(b) => serializer.serialize_bytes(b),
            Value::List(l) => {
                let mut seq = serializer.serialize_seq(Some(l.len()))?;
                for e in l.iter() {
                    seq.serialize_element(&*e.borrow())?;
                }
                seq.end()
            }
            Value::Function(_) => Err(serde::ser::Error::custom("functions are not serializable")),
            Value::Iterator { .. } => {
                Err(serde::ser::Error::custom("iterators are not serializable"))
            }
            Value::Option(None) => serializer.serialize_none(),
            Value::Option(Some(v)) => serializer.serialize_some(&*v),
            Value::Private(_) => Err(serde::ser::Error::custom(
                "private values are not serializable",
            )),
        }
    }
}

macro_rules! as_ty {
    (fn $name:ident -> $ret_ty:ty {
        $variant:ident | expected $expected:expr
    }) => {
        pub(crate) fn $name(&self) -> RuntimeResult<&$ret_ty> {
            match self {
                Value::$variant(v) => Ok(v),
                v => Err(RuntimeError::UnexpectedType {
                    expected: $expected,
                    got: v.ty(),
                }),
            }
        }
    };

    (fn mut $name:ident -> $ret_ty:ty {
        $variant:ident | expected $expected:expr
    }) => {
        pub(crate) fn $name(&mut self) -> RuntimeResult<&mut $ret_ty> {
            match self {
                Value::$variant(v) => Ok(v),
                v => Err(RuntimeError::UnexpectedType {
                    expected: $expected,
                    got: v.ty(),
                }),
            }
        }
    };
}

impl Value {
    pub fn to_string(&self) -> Rc<String> {
        match self {
            Value::Str(v) => v.clone(),
            Value::Int(i) => i.to_string().into(),
            Value::Bytes(v) => String::from_utf8_lossy(v).to_string().into(),
            Value::List(l) => match l.as_slice() {
                [] => "[]".to_owned().into(),
                [x] => format!("[{}]", x.borrow().to_string()).into(),
                [x, rest @ ..] => {
                    let mut str = format!("[{}", x.borrow().to_string());
                    for elem in rest.iter() {
                        str += ",";
                        str += &*elem.borrow().to_string();
                    }
                    str += "]";
                    str.into()
                }
            },
            Value::Option(None) => "None".to_owned().into(),
            Value::Option(Some(v)) => format!("Some({})", v.to_string()).into(),
            Value::Function(f) => f.to_string().into(),
            Value::Iterator(IteratorValue { value, next }) => format!(
                "iterator{{value:{},next:{}}}",
                value.borrow().to_string(),
                next.to_string()
            )
            .into(),
            Value::Private(_) => "<private>".to_owned().into(),
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Value::Str(_) => Type::String,
            Value::Int(_) => Type::Int,
            Value::Bytes(_) => Type::Bytes,
            Value::Option(None) => Type::Option(Box::new(Type::Dynamic)),
            Value::Option(Some(v)) => Type::Option(Box::new(v.ty())),
            Value::List(_) => Type::List(Box::new(Type::Dynamic)),
            Value::Function(_) => todo!(),
            Value::Iterator { .. } => todo!(),
            Value::Private(_) => Type::Private,
        }
    }

    pub(crate) fn as_int(&self) -> RuntimeResult<i64> {
        match self {
            Value::Int(i) => Ok(*i),
            v => Err(RuntimeError::UnexpectedType {
                expected: Type::Int,
                got: v.ty(),
            }),
        }
    }

    as_ty!(fn as_str -> str {
        Str | expected Type::String
    });

    /* as_ty!(fn as_priv -> PrivateValue {
        Private | expected Type::Private
    }); */

    as_ty!(fn mut as_priv_mut -> PrivateValue {
        Private | expected Type::Private
    });

    as_ty!(fn as_iter -> IteratorValue {
        Iterator | expected Type::Iterator(Box::new(Type::Dynamic))
    });
}

pub struct RuntimeCtx<'input> {
    pub shell_ctx: &'input mut ShellContext,
    overlays: Vec<Overlay<'input>>,
    exit: Spur,
}

#[derive(Debug)]
pub struct Overlay<'input> {
    definitions: HashMap<Spur, cow_ast::Expression<'input>>,
    values: HashMap<Spur, Value>,
    currently_evaluating: HashSet<Spur>,
}

fn root_overlay<'input>(sh_ctx: &mut ShellContext) -> Overlay<'input> {
    let mut values = HashMap::new();
    for (id, f) in sh_ctx.builtins.iter().enumerate() {
        values.insert(
            sh_ctx.rodeo.get_or_intern_static(f.name),
            Value::Function(FunctionValue::NativeFn(id as isize)),
        );
    }
    Overlay {
        definitions: HashMap::new(),
        values,
        currently_evaluating: HashSet::new(),
    }
}

impl<'input> RuntimeCtx<'input> {
    fn call_native_function(&mut self, id: isize, args: Vec<Value>) -> RuntimeResult<Value> {
        fn check_args(expected: usize, args: &[Value]) -> RuntimeResult<()> {
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
            // Negative index are private non named functions
            // increment range iterator and return value
            -1 => {
                let it = args[0].as_iter()?;
                let mut value = it.value.borrow_mut();
                match value.as_priv_mut()? {
                    PrivateValue::Range { start, end } if *start < *end => {
                        let ret = *start;
                        *start += 1;
                        Ok(Value::Option(Some(Gc::new(Value::Int(ret)))))
                    }
                    _ => Ok(Value::Option(None)),
                }
            }
            // s
            0 => {
                check_args(1, &args)?;
                Ok(Value::Str(args[0].to_string()))
            }
            // env =>
            1 => {
                check_args(2, &args)?;
                let name = args[0].as_str()?;
                let val = args[1].as_str()?;
                std::env::set_var(name, val);
                Ok(args.into_iter().nth(1).unwrap())
            }
            // json
            2 => {
                check_args(1, &args)?;
                Ok(Value::Str(serde_json::to_string(&args[0])?.into()))
            }
            // range
            3 => {
                check_args(2, &args)?;
                let start = args[0].as_int()?;
                let end = args[1].as_int()?;
                let range = Value::Private(PrivateValue::Range { start, end });
                Ok(Value::Iterator(IteratorValue {
                    value: Gc::new(GcCell::new(range)),
                    next: FunctionValue::NativeFn(-1),
                }))
            }
            // next
            4 => {
                check_args(1, &args)?;
                let it = args[0].as_iter()?;
                let next = self.call_function_value(&it.next, vec![args[0].clone()]);
                next
            }
            _ => unreachable!("invalid native function got called ({})", id),
        }
    }

    pub fn new(shell_ctx: &'input mut ShellContext) -> Self {
        Self {
            exit: shell_ctx.rodeo.get_or_intern_static("exit"),
            overlays: vec![root_overlay(shell_ctx)],
            shell_ctx,
        }
    }

    fn update_overlay(&mut self, definition: cow_ast::VariableDefinition<'input>) {
        let ov = self
            .overlays
            .last_mut()
            .expect("Should always have an overlay");
        ov.currently_evaluating.remove(&definition.name);
        ov.values.remove(&definition.name);
        ov.definitions.insert(definition.name, definition.expr);
    }

    fn enter_overlay(&mut self, definitions: Vec<cow_ast::VariableDefinition<'input>>) {
        let overlay = Overlay {
            values: HashMap::new(),
            definitions: definitions
                .into_iter()
                .map(|def| (def.name, def.expr))
                .collect(),
            currently_evaluating: HashSet::new(),
        };
        self.overlays.push(overlay);
    }

    fn enter_single_overlay(&mut self, definition: cow_ast::VariableDefinition<'input>) {
        let overlay = Overlay {
            values: HashMap::new(),
            definitions: {
                let mut map = HashMap::new();
                map.insert(definition.name, definition.expr);
                map
            },
            currently_evaluating: HashSet::new(),
        };
        self.overlays.push(overlay);
    }

    pub(crate) fn prepare_cmd(
        &mut self,
        command: &cow_ast::Command<'input>,
    ) -> RuntimeResult<process::Command> {
        let name = self.eval_expr(&command.name)?.to_string();
        if &*name == "exit" {
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
        pipeline: &cow_ast::Pipeline<'input>,
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

    fn run_pipeline(&mut self, pipeline: &cow_ast::Pipeline<'input>) -> RuntimeResult<ExitStatus> {
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

    fn run_chain_part(&mut self, chain_part: &cow_ast::ChainPart<'input>) -> RuntimeResult<ExitStatus> {
        match chain_part {
            cow_ast::ChainPart::Pipeline(p) => self.run_pipeline(p),
            cow_ast::ChainPart::Chain(c) => self.run_chain(c),
        }
    }

    fn run_chain(&mut self, chain: &cow_ast::CommandChain<'input>) -> RuntimeResult<ExitStatus> {
        match chain {
            cow_ast::CommandChain::Or(c, rest) => {
                let result = self.run_chain_part(c)?;
                if result.success() {
                    Ok(result)
                } else {
                    self.run_chain(rest)
                }
            }
            cow_ast::CommandChain::And(c, rest) => {
                let result = self.run_chain_part(c)?;
                if result.success() {
                    self.run_chain(rest)
                } else {
                    Ok(result)
                }
            }
            cow_ast::CommandChain::Pipeline(p) => self.run_pipeline(p),
        }
    }

    pub fn run_cmd_stmt(&mut self, cmd_stmt: cow_ast::CommandStatement<'input>) -> RuntimeResult<()> {
        match cmd_stmt {
            cow_ast::CommandStatement::Definitions(defs) => {
                defs.into_iter().for_each(|def| self.update_overlay(def))
            }
            cow_ast::CommandStatement::Commands(ctx) => self.run_cmd_ctx(ctx)?,
        }

        Ok(())
    }

    pub fn run_cmd_ctx(&mut self, cmd_ctx: cow_ast::CommandContext<'input>) -> RuntimeResult<()> {
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
        fstring: &[cow_ast::StringPart<'input>],
    ) -> RuntimeResult<Rc<String>> {
        match fstring {
            [cow_ast::StringPart::Text(v)] => Ok(Rc::from(v.to_string())),
            [cow_ast::StringPart::Variable(v)] => self.resolve_text(*v),
            [cow_ast::StringPart::Expression(e)] => Ok(self.eval_expr(e)?.to_string()),
            _ => fstring
                .iter()
                .try_fold(String::new(), |mut current, segment| -> RuntimeResult<_> {
                    match segment {
                        cow_ast::StringPart::Text(s) => current.push_str(s),
                        cow_ast::StringPart::Variable(v) => current.push_str(&self.resolve_text(*v)?),
                        cow_ast::StringPart::Expression(e) => {
                            current.push_str(&self.eval_expr(e)?.to_string())
                        }
                    }
                    Ok(current)
                })
                .map(Rc::from),
        }
    }

    fn resolve_text(&mut self, name: Spur) -> RuntimeResult<Rc<String>> {
        match self.resolve(name)? {
            None => {
                eprintln!(
                    "Warning: {} was not defined",
                    self.shell_ctx
                        .rodeo
                        .try_resolve(&name)
                        .unwrap_or("<unknown>")
                );
                Ok("".to_owned().into())
            }
            Some(v) => Ok(v.to_string()),
        }
    }

    fn rec_resolve(&mut self, name: Spur) -> RuntimeResult<Option<Value>> {
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

    fn resolve(&mut self, name: Spur) -> RuntimeResult<Option<Value>> {
        if name == self.exit {
            Ok(Some(Value::Int(
                self.shell_ctx
                    .last_exit
                    .map(|v| v.code())
                    .flatten()
                    .unwrap_or(0) as i64,
            )))
        } else {
            self.rec_resolve(name)
        }
    }

    fn call_function(&mut self, function: &Value, args: Vec<Value>) -> RuntimeResult<Value> {
        match function {
            Value::Function(f) => self.call_function_value(f, args),
            val => return Err(RuntimeError::UncallableType(val.ty())),
        }
    }

    fn call_function_value(
        &mut self,
        function_value: &FunctionValue,
        args: Vec<Value>,
    ) -> RuntimeResult<Value> {
        match function_value {
            FunctionValue::NativeFn(id) => self.call_native_function(*id, args),
        }
    }

    fn eval_expr(&mut self, expr: &cow_ast::Expression<'input>) -> RuntimeResult<Value> {
        match expr {
            cow_ast::Expression::SubShell(code) => Ok(Value::Bytes(Rc::new(
                process::Command::new(std::env::current_exe()?)
                    .arg("builtin")
                    .arg("run-ast")
                    .arg("-b")
                    .arg(base64::encode(bincode::serialize(code)?))
                    .output()?
                    .stdout,
            ))),
            cow_ast::Expression::Value(v) => match v {
                cow_ast::Value::String(s) => Ok(Value::Str(Rc::from(s.to_string()))),
                cow_ast::Value::Int(i) => Ok(Value::Int(*i)),
                cow_ast::Value::List(l) => Ok(Value::List(Gc::new(
                    l.iter()
                        .map(|expr| -> RuntimeResult<_> { Ok(GcCell::new(self.eval_expr(expr)?)) })
                        .collect::<RuntimeResult<_>>()?,
                ))),
            },
            cow_ast::Expression::Call { function, args } => {
                let function = self.eval_expr(function)?;
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.eval_expr(arg))
                    .collect::<RuntimeResult<_>>()?;
                self.call_function(&function, args)
            }
            cow_ast::Expression::Method { value, name, args } => {
                let args = std::iter::once(&**value)
                    .chain(args.iter())
                    .map(|arg| self.eval_expr(arg))
                    .collect::<RuntimeResult<_>>()?;
                match self.resolve(*name)? {
                    None => Err(RuntimeError::Undefined(
                        self.shell_ctx
                            .rodeo
                            .try_resolve(name)
                            .unwrap_or("<unkown>")
                            .to_owned(),
                    )),
                    Some(function) => self.call_function(&function, args),
                }
            }
            cow_ast::Expression::Interpolated(i) => self.run_interpolation(i).map(Value::Str),
            cow_ast::Expression::Variable(v) => self.resolve(*v)?.map(Ok).unwrap_or_else(|| {
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

    pub fn run_statement(&mut self, statement: Statement<'input>) -> RuntimeResult<()> {
        match statement {
            Statement::VarDef(v) => {
                self.enter_single_overlay(v);
            }
            Statement::Cmd {
                blk,
                capture: _capture,
            } => {
                for cmd in blk {
                    self.run_cmd_stmt(cmd)?;
                }
            }
        }
        Ok(())
    }
}
