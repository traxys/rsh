use crate::{
    ast::TypeCheck,
    cow_ast::{self, RedirectionType, Statement, StatementGroup, Type},
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
    io::Read,
    process::{self, ExitStatus, Stdio},
    rc::Rc,
    sync::atomic,
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
    #[error("tried to unwrap None")]
    UnwrapedNone,
    #[error("expression is not assignable")]
    Unasignable,
    #[error("interupted")]
    Interupted,
}

#[derive(Debug, Clone, Trace, Finalize)]
// TODO: optimize such that we don't need to box everything like numbers for example
enum Value {
    Str(Rc<String>),
    Int(i64),
    Bytes(Rc<Vec<u8>>),
    Function(FunctionValue),
    List(Gc<Vec<GcCell<Gc<Value>>>>),
    Iterator(IteratorValue),
    Option(Option<Gc<Value>>),
    Private(PrivateValue),
    Bool(bool),
    Unit,
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
    User(usize),
}

impl FunctionValue {
    fn to_string(&self, rt_ctx: &mut RuntimeCtx) -> String {
        match self {
            FunctionValue::NativeFn(id) if *id >= 0 => {
                format!(
                    "<native fn {}>",
                    rt_ctx.shell_ctx.builtins[*id as usize].name
                )
            }
            FunctionValue::NativeFn(id) => {
                format!("<private native fn {}>", -id)
            }
            FunctionValue::User(_) => todo!(),
        }
    }

    fn ty(&self, closures: &[Closure], sh_ctx: &mut ShellContext) -> Type {
        match self {
            FunctionValue::NativeFn(x) => sh_ctx.builtins[*x as usize].ty(),
            FunctionValue::User(id) => {
                let f = &closures[*id];
                Type::Function {
                    ret: Box::new(f.ret.clone()),
                    args: f.args.iter().map(|(_, t)| t.clone()).collect(),
                }
            }
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
            Value::Unit => serializer.serialize_unit(),
            Value::Bool(b) => serializer.serialize_bool(*b),
        }
    }
}

macro_rules! as_ty {
    (fn $name:ident -> $ret_ty:ty {
        $variant:ident | expected $expected:expr
    }) => {
        pub(crate) fn $name(
            &self,
            closures: &[Closure],
            sh_ctx: &mut ShellContext,
        ) -> RuntimeResult<&$ret_ty> {
            match self {
                Value::$variant(v) => Ok(v),
                v => Err(RuntimeError::UnexpectedType {
                    expected: $expected,
                    got: v.ty(closures, sh_ctx),
                }),
            }
        }
    };

    (fn mut $name:ident -> $ret_ty:ty {
        $variant:ident | expected $expected:expr
    }) => {
        pub(crate) fn $name(
            &mut self,
            closures: &[Closure],
            sh_ctx: &mut ShellContext,
        ) -> RuntimeResult<&mut $ret_ty> {
            match self {
                Value::$variant(v) => Ok(v),
                v => Err(RuntimeError::UnexpectedType {
                    expected: $expected,
                    got: v.ty(closures, sh_ctx),
                }),
            }
        }
    };
}

impl Value {
    pub fn to_string(&self, rt_ctx: &mut RuntimeCtx) -> Rc<String> {
        match self {
            Value::Str(v) => v.clone(),
            Value::Int(i) => i.to_string().into(),
            Value::Bytes(v) => String::from_utf8_lossy(v).to_string().into(),
            Value::List(l) => match l.as_slice() {
                [] => "[]".to_owned().into(),
                [x] => format!("[{}]", x.borrow().to_string(rt_ctx)).into(),
                [x, rest @ ..] => {
                    let mut str = format!("[{}", x.borrow().to_string(rt_ctx));
                    for elem in rest.iter() {
                        str += ",";
                        str += &*elem.borrow().to_string(rt_ctx);
                    }
                    str += "]";
                    str.into()
                }
            },
            Value::Option(None) => "None".to_owned().into(),
            Value::Option(Some(v)) => format!("Some({})", v.to_string(rt_ctx)).into(),
            Value::Function(f) => f.to_string(rt_ctx).into(),
            Value::Iterator(IteratorValue { value, next }) => format!(
                "iterator{{value:{},next:{}}}",
                value.borrow().to_string(rt_ctx),
                next.to_string(rt_ctx)
            )
            .into(),
            Value::Private(_) => "<private>".to_owned().into(),
            Value::Unit => "()".to_owned().into(),
            Value::Bool(b) => b.to_string().into(),
        }
    }

    pub fn ty(&self, closures: &[Closure], sh_ctx: &mut ShellContext) -> Type {
        match self {
            Value::Str(_) => Type::String,
            Value::Int(_) => Type::Int,
            Value::Bytes(_) => Type::Bytes,
            Value::Option(None) => Type::Option(Box::new(Type::Dynamic)),
            Value::Option(Some(v)) => Type::Option(Box::new(v.ty(closures, sh_ctx))),
            Value::List(l) => {
                if l.is_empty() {
                    Type::List(Box::new(Type::Dynamic))
                } else {
                    let ty = l.first().unwrap().borrow().ty(closures, sh_ctx);
                    for v in l.iter().skip(1) {
                        if ty.is_compatible(&v.borrow().ty(closures, sh_ctx))
                            != TypeCheck::Compatible
                        {
                            return Type::List(Box::new(Type::Dynamic));
                        }
                    }
                    Type::List(Box::new(ty))
                }
            }
            Value::Function(f) => f.ty(closures, sh_ctx),
            Value::Iterator { .. } => todo!(),
            Value::Private(_) => Type::Private,
            Value::Unit => Type::Unit,
            Value::Bool(_) => Type::Bool,
        }
    }

    pub fn type_checks(
        &self,
        ty: &Type,
        closures: &[Closure],
        sh_ctx: &mut ShellContext,
    ) -> RuntimeResult<()> {
        match (self, ty) {
            (_, Type::Dynamic) => Ok(()),
            (Value::Str(_), Type::String) => Ok(()),
            (Value::Int(_), Type::Int) => Ok(()),
            (Value::Bytes(_), Type::String | Type::Bytes) => Ok(()),
            (Value::Unit, Type::Unit) => Ok(()),
            (Value::Option(inner), Type::Option(inner_ty)) => match inner {
                Some(inner) => inner.type_checks(&inner_ty, closures, sh_ctx),
                None => Ok(()),
            },
            (Value::Private(_), _) => todo!(),
            (Value::Function(f), Type::Function { ret, args }) => {
                let (vret, vargs) = match f.ty(closures, sh_ctx) {
                    Type::Function { ret, args } => (ret, args),
                    _ => unreachable!(),
                };
                if (**ret != Type::Dynamic && *vret != **ret)
                    || args.len() != vargs.len()
                    || args
                        .iter()
                        .zip(&vargs)
                        .any(|(t, vt)| *vt != Type::Dynamic && *vt != *t)
                {
                    Err(RuntimeError::UnexpectedType {
                        expected: Type::Function {
                            ret: ret.clone(),
                            args: args.clone(),
                        },
                        got: Type::Function {
                            ret: vret,
                            args: vargs,
                        },
                    })
                } else {
                    Ok(())
                }
            }
            (Value::List(l), Type::List(l_ty)) => {
                for x in l.iter() {
                    x.borrow().type_checks(l_ty, closures, sh_ctx)?;
                }
                Ok(())
            }
            (Value::Iterator(_), Type::Iterator(_)) => todo!(),
            (_, _) => Err(RuntimeError::UnexpectedType {
                expected: ty.clone(),
                got: self.ty(closures, sh_ctx),
            }),
        }
    }

    pub(crate) fn as_int(
        &self,
        closures: &[Closure],
        sh_ctx: &mut ShellContext,
    ) -> RuntimeResult<i64> {
        match self {
            Value::Int(i) => Ok(*i),
            v => Err(RuntimeError::UnexpectedType {
                expected: Type::Int,
                got: v.ty(closures, sh_ctx),
            }),
        }
    }

    as_ty!(fn as_str -> str {
        Str | expected Type::String
    });

    as_ty!(fn as_bool -> bool {
        Bool | expected Type::Bool
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

struct Closure<'input> {
    ret: Type,
    args: Vec<(Spur, Type)>,
    body: StatementGroup<'input>,
    captures: Vec<(Spur, Gc<Value>)>,
}

#[derive(Debug)]
enum StatementExec {
    NoAction,
    Break(Value),
    Return(Value),
}

// TODO: fix leak of closures
pub struct RuntimeCtx<'input> {
    pub shell_ctx: &'input mut ShellContext,
    overlays: Vec<Overlay<'input>>,
    closures: Vec<Closure<'input>>,
    exit: Spur,
}

#[derive(Debug)]
pub struct Overlay<'input> {
    definitions: HashMap<Spur, cow_ast::Expression<'input>>,
    types: HashMap<Spur, Type>,
    values: HashMap<Spur, Gc<Value>>,
    currently_evaluating: HashSet<Spur>,
}

fn root_overlay<'input>(sh_ctx: &mut ShellContext) -> Overlay<'input> {
    let mut values = HashMap::new();
    let mut types = HashMap::new();
    for (id, f) in sh_ctx.builtins.iter().enumerate() {
        let spur = sh_ctx.rodeo.get_or_intern_static(f.name);
        values.insert(
            spur,
            Gc::new(Value::Function(FunctionValue::NativeFn(id as isize))),
        );
        types.insert(spur, f.ty());
    }
    Overlay {
        definitions: HashMap::new(),
        values,
        types,
        currently_evaluating: HashSet::new(),
    }
}

struct CaptureCtx {
    defined: Vec<HashSet<Spur>>,
    undefined: HashSet<Spur>,
}

impl CaptureCtx {
    fn process_id(&mut self, name: Spur) {
        if !self.defined.iter().any(|set| set.contains(&name)) {
            self.undefined.insert(name);
        }
    }

    fn process_body(&mut self, body: &StatementGroup) {
        for stmt in &body.group {
            self.process_statement(stmt);
        }
        if let Some(e) = &body.ret {
            self.process_expr(e);
        }
    }

    fn process_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::VarDef(def) => {
                self.defined.last_mut().unwrap().insert(def.name);
            }
            Statement::Cmd { blk, capture } => {
                self.defined.push(HashSet::new());
                for stmt in blk {
                    self.process_command_statement(stmt);
                }
                self.defined.pop();

                if let Some(cpt) = capture {
                    self.defined.last_mut().unwrap().insert(*cpt);
                }
            }
            Statement::Expr(e) => self.process_expr(e),
            Statement::Assign { lhs, rhs } => {
                self.process_expr(rhs);
                self.process_expr(lhs);
            }
            Statement::Branch(b) => self.process_branch(b),
        }
    }

    fn process_branch(&mut self, branch: &cow_ast::Branch) {
        match branch {
            cow_ast::Branch::If(_) => todo!(),
            cow_ast::Branch::Loop(l) => {
                for s in l {
                    self.defined.push(HashSet::new());
                    self.process_statement(s);
                    self.defined.pop();
                }
            }
        }
    }

    fn process_command_statement(&mut self, cmd_stmt: &cow_ast::CommandStatement) {
        match cmd_stmt {
            cow_ast::CommandStatement::Definitions(defs) => self.process_defs(defs),
            cow_ast::CommandStatement::Commands(cmd) => self.process_cmd_ctx(cmd),
        }
    }

    fn process_defs(&mut self, defs: &[cow_ast::VariableDefinition]) {
        self.defined
            .last_mut()
            .unwrap()
            .extend(defs.iter().map(|def| def.name));
        for def in defs {
            self.process_expr(&def.expr);
        }
    }

    fn process_cmd_ctx(&mut self, cmd_ctx: &cow_ast::CommandContext) {
        self.defined.push(HashSet::new());
        self.process_defs(&cmd_ctx.variables);
        for chain in &cmd_ctx.commands {
            self.process_cmd_chain(chain);
        }
        self.defined.pop();
    }

    fn process_cmd_chain(&mut self, chain: &cow_ast::CommandChain) {
        match chain {
            cow_ast::CommandChain::Or(part, chain) | cow_ast::CommandChain::And(part, chain) => {
                self.process_part(part);
                self.process_cmd_chain(chain);
            }
            cow_ast::CommandChain::Pipeline(pipeline) => self.process_pipeline(pipeline),
        }
    }

    fn process_part(&mut self, part: &cow_ast::ChainPart) {
        match part {
            cow_ast::ChainPart::Pipeline(p) => self.process_pipeline(p),
            cow_ast::ChainPart::Chain(c) => self.process_cmd_chain(c),
        }
    }

    fn process_pipeline(&mut self, pipeline: &cow_ast::Pipeline) {
        for cmd in &pipeline.commands {
            self.process_command(cmd);
        }
    }

    fn process_command(&mut self, command: &cow_ast::Command) {
        self.process_expr(&command.name);
        for arg in &command.args {
            self.process_expr(arg);
        }
        for (_, redir) in &command.redirections {
            self.process_expr(redir);
        }
    }

    fn process_expr(&mut self, expr: &cow_ast::Expression) {
        match expr {
            cow_ast::Expression::Value(v) => match v {
                cow_ast::Value::String(_) => (),
                cow_ast::Value::Int(_) => (),
                cow_ast::Value::Bool(_) => (),
                cow_ast::Value::List(l) => {
                    for expr in l {
                        self.process_expr(expr);
                    }
                }
            },
            cow_ast::Expression::Call { function, args } => {
                self.process_expr(function);
                for arg in args {
                    self.process_expr(arg);
                }
            }
            cow_ast::Expression::Method { value, name, args } => {
                self.process_id(*name);
                self.process_expr(value);
                for arg in args {
                    self.process_expr(arg);
                }
            }
            cow_ast::Expression::Interpolated(parts) => self.process_string_parts(parts),
            cow_ast::Expression::SubShell(cmd_ctx) => self.process_cmd_ctx(cmd_ctx),
            cow_ast::Expression::Variable(name) => self.process_id(*name),
            cow_ast::Expression::FuncDef { args, ret: _, body } => {
                self.defined
                    .push(args.iter().map(|(name, _)| *name).collect());
                self.process_body(body);
                self.defined.pop();
            }
            cow_ast::Expression::Unwrap(v) => self.process_expr(v),
            cow_ast::Expression::Cond {
                cond,
                br_if,
                br_else,
            } => {
                self.process_expr(cond);

                self.defined.push(HashSet::new());
                self.process_body(br_if);
                self.defined.pop();

                self.defined.push(HashSet::new());
                self.process_body(br_else);
                self.defined.pop();
            }
        }
    }

    fn process_string_parts(&mut self, parts: &[cow_ast::StringPart]) {
        for part in parts {
            match part {
                cow_ast::StringPart::Text(_) => (),
                cow_ast::StringPart::Variable(n) => self.process_id(*n),
                cow_ast::StringPart::Expression(e) => self.process_expr(e),
            }
        }
    }
}

impl<'input> RuntimeCtx<'input> {
    fn call_native_function(
        &mut self,
        id: isize,
        args: Vec<Gc<Value>>,
    ) -> RuntimeResult<Gc<Value>> {
        fn check_args(expected: usize, args: &[Gc<Value>]) -> RuntimeResult<()> {
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
                let it = args[0].as_iter(&self.closures, self.shell_ctx)?;
                let mut value = it.value.borrow_mut();
                match value.as_priv_mut(&self.closures, self.shell_ctx)? {
                    PrivateValue::Range { start, end } if *start < *end => {
                        let ret = *start;
                        *start += 1;
                        Ok(Gc::new(Value::Option(Some(Gc::new(Value::Int(ret))))))
                    }
                    _ => Ok(Gc::new(Value::Option(None))),
                }
            }
            // s
            0 => {
                check_args(1, &args)?;
                Ok(Gc::new(Value::Str(args[0].to_string(self))))
            }
            // env =>
            1 => {
                check_args(2, &args)?;
                let name = args[0].as_str(&self.closures, self.shell_ctx)?;
                let val = args[1].as_str(&self.closures, self.shell_ctx)?;
                std::env::set_var(name, val);
                Ok(args.into_iter().nth(1).unwrap())
            }
            // json
            2 => {
                check_args(1, &args)?;
                Ok(Gc::new(Value::Str(serde_json::to_string(&args[0])?.into())))
            }
            // range
            3 => {
                check_args(2, &args)?;
                let start = args[0].as_int(&self.closures, self.shell_ctx)?;
                let end = args[1].as_int(&self.closures, self.shell_ctx)?;
                let range = Value::Private(PrivateValue::Range { start, end });
                Ok(Gc::new(Value::Iterator(IteratorValue {
                    value: Gc::new(GcCell::new(range)),
                    next: FunctionValue::NativeFn(-1),
                })))
            }
            // next
            4 => {
                check_args(1, &args)?;
                let it = args[0].as_iter(&self.closures, self.shell_ctx)?;
                let next = self.call_function_value(&it.next, vec![args[0].clone()]);
                next
            }
            // print
            // TODO: capture print when required
            5 => {
                check_args(1, &args)?;
                print!("{}", args[0].to_string(self));
                Ok(Gc::new(Value::Unit))
            }
            _ => unreachable!("invalid native function got called ({})", id),
        }
    }

    pub fn new(shell_ctx: &'input mut ShellContext) -> Self {
        Self {
            exit: shell_ctx.rodeo.get_or_intern_static("exit"),
            overlays: vec![root_overlay(shell_ctx)],
            closures: Vec::new(),
            shell_ctx,
        }
    }

    fn check_interupted(&self) -> RuntimeResult<()> {
        if self.shell_ctx.interrupted.load(atomic::Ordering::Relaxed) {
            Err(RuntimeError::Interupted)
        } else {
            Ok(())
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
        let (definitions, types) = definitions
            .into_iter()
            .map(|def| ((def.name, def.expr), (def.name, def.ty)))
            .unzip();
        let overlay = Overlay {
            values: HashMap::new(),
            definitions,
            types,
            currently_evaluating: HashSet::new(),
        };
        self.overlays.push(overlay);
    }

    fn add_to_overlay(&mut self, definition: cow_ast::VariableDefinition<'input>) {
        let ov = self.overlays.last_mut().unwrap();
        ov.definitions.insert(definition.name, definition.expr);
        ov.types.insert(definition.name, definition.ty);
    }

    pub(crate) fn prepare_cmd(
        &mut self,
        command: &cow_ast::Command<'input>,
    ) -> RuntimeResult<process::Command> {
        let name = self.eval_expr(&command.name)?.to_string(self);
        if &*name == "exit" {
            if command.args.len() > 1 {
                return Err(RuntimeError::Exit(255));
            }

            match command
                .args
                .first()
                .map(|v| self.eval_expr(v).map(|v| v.to_string(self).parse()))
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
            .map(|v| self.eval_expr(v).map(|v| v.to_string(self)))
            .collect::<RuntimeResult<_>>()?;
        cmd.args(args.iter().map(|x| x.as_ref()));

        for (ty, path) in &command.redirections {
            let path = self.eval_expr(&path)?.to_string(self);
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
        save_output: bool,
    ) -> RuntimeResult<(Vec<process::Child>, process::Command)> {
        let mut prepared: Vec<_> = pipeline
            .commands
            .iter()
            .map(|c| self.prepare_cmd(c))
            .collect::<RuntimeResult<_>>()?;
        if prepared.len() == 1 {
            let mut last = prepared.pop().unwrap();

            if save_output {
                last.stdout(Stdio::piped());
            }

            return Ok((vec![], last));
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

            if save_output {
                last.stdout(Stdio::piped());
            }

            Ok((children, last))
        }
    }

    fn run_pipeline(
        &mut self,
        pipeline: &cow_ast::Pipeline<'input>,
        output: Option<&mut Vec<u8>>,
    ) -> RuntimeResult<ExitStatus> {
        let (mut children, mut last) = self.prepare_pipeline(pipeline, output.is_some())?;
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
        let child = self.shell_ctx.current_process.write().unwrap().take();
        if let Some(out) = output {
            if let Some(child) = child {
                if let Some(mut stdout) = child.into_inner().stdout {
                    stdout.read_to_end(out)?;
                }
            }
        }

        children.iter_mut().for_each(|p| {
            let _ = p.kill();
        });

        res
    }

    fn run_chain_part(
        &mut self,
        chain_part: &cow_ast::ChainPart<'input>,
        output: Option<&mut Vec<u8>>,
    ) -> RuntimeResult<ExitStatus> {
        match chain_part {
            cow_ast::ChainPart::Pipeline(p) => self.run_pipeline(p, output),
            cow_ast::ChainPart::Chain(c) => self.run_chain(c, output),
        }
    }

    fn run_chain(
        &mut self,
        chain: &cow_ast::CommandChain<'input>,
        mut output: Option<&mut Vec<u8>>,
    ) -> RuntimeResult<ExitStatus> {
        match chain {
            cow_ast::CommandChain::Or(c, rest) => {
                let result = self.run_chain_part(c, output.as_deref_mut())?;
                if result.success() {
                    Ok(result)
                } else {
                    self.run_chain(rest, output)
                }
            }
            cow_ast::CommandChain::And(c, rest) => {
                let result = self.run_chain_part(c, output.as_deref_mut())?;
                if result.success() {
                    self.run_chain(rest, output)
                } else {
                    Ok(result)
                }
            }
            cow_ast::CommandChain::Pipeline(p) => self.run_pipeline(p, output),
        }
    }

    pub fn run_cmd_stmt(
        &mut self,
        cmd_stmt: cow_ast::CommandStatement<'input>,
        output: Option<&mut Vec<u8>>,
    ) -> RuntimeResult<()> {
        match cmd_stmt {
            cow_ast::CommandStatement::Definitions(defs) => {
                defs.into_iter().for_each(|def| self.update_overlay(def))
            }
            cow_ast::CommandStatement::Commands(ctx) => self.run_cmd_ctx(ctx, output)?,
        }

        Ok(())
    }

    pub fn run_cmd_ctx(
        &mut self,
        cmd_ctx: cow_ast::CommandContext<'input>,
        mut output: Option<&mut Vec<u8>>,
    ) -> RuntimeResult<()> {
        TypeCheckerCtx::new(self.shell_ctx)
            .check_cmd_ctx(&cmd_ctx)
            .map_err(|ty_errs| RuntimeError::Static(ty_errs))?;

        self.enter_overlay(cmd_ctx.variables);

        for command in &cmd_ctx.commands {
            self.shell_ctx.last_exit = Some(self.run_chain(command, output.as_deref_mut())?);
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
            [cow_ast::StringPart::Expression(e)] => Ok(self.eval_expr(e)?.to_string(self)),
            _ => fstring
                .iter()
                .try_fold(String::new(), |mut current, segment| -> RuntimeResult<_> {
                    match segment {
                        cow_ast::StringPart::Text(s) => current.push_str(s),
                        cow_ast::StringPart::Variable(v) => {
                            current.push_str(&self.resolve_text(*v)?)
                        }
                        cow_ast::StringPart::Expression(e) => {
                            current.push_str(&self.eval_expr(e)?.to_string(self))
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
            Some(v) => Ok(v.to_string(self)),
        }
    }

    fn rec_resolve(&mut self, name: Spur) -> RuntimeResult<Option<Gc<Value>>> {
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
            let ty = overlay.types.get(&name).unwrap_or(&Type::Dynamic);
            val.type_checks(ty, &self.closures, self.shell_ctx)?;
            overlay.values.insert(name, val.clone());
            return Ok(Some(val));
        }

        // TODO: Env Var
        Ok(None)
    }

    fn resolve(&mut self, name: Spur) -> RuntimeResult<Option<Gc<Value>>> {
        if name == self.exit {
            Ok(Some(Gc::new(Value::Int(
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

    fn call_function(
        &mut self,
        function: &Value,
        args: Vec<Gc<Value>>,
    ) -> RuntimeResult<Gc<Value>> {
        match function {
            Value::Function(f) => self.call_function_value(f, args),
            val => {
                return Err(RuntimeError::UncallableType(
                    val.ty(&self.closures, self.shell_ctx),
                ))
            }
        }
    }

    fn call_user_function(&mut self, id: usize, args: Vec<Gc<Value>>) -> RuntimeResult<Gc<Value>> {
        let Self {
            closures,
            shell_ctx,
            ..
        } = self;
        let f = &closures[id];
        if f.args.len() != args.len() {
            return Err(RuntimeError::InvalidArgCount {
                expected: f.args.len(),
                got: args.len(),
            });
        };
        let (values, types) = f.args.iter().zip(&args).try_fold(
            (
                HashMap::with_capacity(args.len()),
                HashMap::with_capacity(args.len()),
            ),
            |(mut vals, mut tys), ((name, ty), val)| -> RuntimeResult<_> {
                val.type_checks(&ty, closures, shell_ctx)?;
                vals.insert(*name, val.clone());
                tys.insert(*name, ty.clone());
                Ok((vals, tys))
            },
        )?;

        let args_overlay = Overlay {
            definitions: HashMap::new(),
            values,
            types,
            currently_evaluating: HashSet::new(),
        };

        let (types, values) = f
            .captures
            .iter()
            .map(|(name, val)| ((*name, val.ty(&closures, shell_ctx)), (*name, val.clone())))
            .unzip();

        let capture_overlay = Overlay {
            definitions: HashMap::new(),
            values,
            types,
            currently_evaluating: HashSet::new(),
        };

        let mut func_ctx = RuntimeCtx {
            shell_ctx: self.shell_ctx,
            overlays: vec![capture_overlay, args_overlay],
            closures: Vec::new(),
            exit: self.exit,
        };

        for statement in &f.body.group {
            match func_ctx.run_statement(statement)? {
                StatementExec::NoAction => (),
                StatementExec::Return(_) => todo!(),
                StatementExec::Break(_) => todo!(),
            }
        }

        match &f.body.ret {
            Some(v) => func_ctx.eval_expr(v),
            None => Ok(Gc::new(Value::Unit)),
        }
    }

    fn call_function_value(
        &mut self,
        function_value: &FunctionValue,
        args: Vec<Gc<Value>>,
    ) -> RuntimeResult<Gc<Value>> {
        match function_value {
            FunctionValue::NativeFn(id) => self.call_native_function(*id, args),
            FunctionValue::User(id) => self.call_user_function(*id, args),
        }
    }

    fn eval_expr(&mut self, expr: &cow_ast::Expression<'input>) -> RuntimeResult<Gc<Value>> {
        match expr {
            cow_ast::Expression::SubShell(code) => Ok(Gc::new(Value::Bytes(Rc::new(
                process::Command::new(std::env::current_exe()?)
                    .arg("builtin")
                    .arg("run-ast")
                    .arg("-b")
                    .arg(base64::encode(bincode::serialize(code)?))
                    .output()?
                    .stdout,
            )))),
            cow_ast::Expression::Value(v) => match v {
                cow_ast::Value::String(s) => Ok(Gc::new(Value::Str(Rc::from(s.to_string())))),
                cow_ast::Value::Int(i) => Ok(Gc::new(Value::Int(*i))),
                cow_ast::Value::List(l) => Ok(Gc::new(Value::List(Gc::new(
                    l.iter()
                        .map(|expr| -> RuntimeResult<_> { Ok(GcCell::new(self.eval_expr(expr)?)) })
                        .collect::<RuntimeResult<_>>()?,
                )))),
                cow_ast::Value::Bool(b) => Ok(Gc::new(Value::Bool(*b))),
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
            cow_ast::Expression::Interpolated(i) => {
                self.run_interpolation(i).map(Value::Str).map(Gc::new)
            }
            cow_ast::Expression::Variable(v) => self.resolve(*v)?.map(Ok).unwrap_or_else(|| {
                Err(RuntimeError::Undefined(
                    self.shell_ctx
                        .rodeo
                        .try_resolve(v)
                        .unwrap_or("<unkown>")
                        .to_owned(),
                ))
            }),
            cow_ast::Expression::FuncDef { args, ret, body } => {
                let idx = self.closures.len();

                let mut capture_ctx = CaptureCtx {
                    defined: vec![args.iter().map(|(name, _)| *name).collect()],
                    undefined: HashSet::new(),
                };

                capture_ctx.process_body(body);

                let captures = capture_ctx
                    .undefined
                    .into_iter()
                    .map(|name| -> RuntimeResult<_> {
                        Ok((
                            name,
                            match self.rec_resolve(name)? {
                                Some(v) => v,
                                None => {
                                    return Err(RuntimeError::Undefined(
                                        self.shell_ctx
                                            .rodeo
                                            .try_resolve(&name)
                                            .unwrap_or("<unkown>")
                                            .to_owned(),
                                    ))
                                }
                            },
                        ))
                    })
                    .collect::<Result<_, _>>()?;

                self.closures.push(Closure {
                    ret: ret.clone(),
                    args: args.clone(),
                    body: body.clone(),
                    captures,
                });
                Ok(Gc::new(Value::Function(FunctionValue::User(idx))))
            }
            cow_ast::Expression::Unwrap(v) => {
                let val = self.eval_expr(v)?;
                match &*val {
                    Value::Option(o) => match o {
                        Some(v) => Ok(v.clone()),
                        None => Err(RuntimeError::UnwrapedNone),
                    },
                    invalid => Err(RuntimeError::UnexpectedType {
                        expected: Type::Option(Box::new(Type::Dynamic)),
                        got: invalid.ty(&self.closures, self.shell_ctx),
                    }),
                }
            }
            cow_ast::Expression::Cond {
                cond,
                br_if,
                br_else,
            } => {
                let cond = *self
                    .eval_expr(cond)?
                    .as_bool(&self.closures, self.shell_ctx)?;

                if cond {
                    self.run_statement_group(br_if)
                } else {
                    self.run_statement_group(br_else)
                }
            }
        }
    }

    fn set_value(&mut self, spur: Spur, value: Value) -> RuntimeResult<()> {
        let ov = self.overlays.last_mut().unwrap();
        let ty = ov.types.get(&spur).unwrap_or(&Type::Dynamic);
        value.type_checks(ty, &self.closures, self.shell_ctx)?;
        ov.values.insert(spur, Gc::new(value));
        Ok(())
    }

    fn run_statement_group(
        &mut self,
        statement_group: &StatementGroup<'input>,
    ) -> RuntimeResult<Gc<Value>> {
        self.enter_overlay(Vec::new());

        for stmt in &statement_group.group {
            self.run_statement(stmt)?;
        }

        let ret = match &statement_group.ret {
            None => Ok(Gc::new(Value::Unit)),
            Some(e) => self.eval_expr(e),
        };

        self.overlays.pop();

        ret
    }

    fn run_statement(&mut self, statement: &Statement<'input>) -> RuntimeResult<StatementExec> {
        self.check_interupted()?;
        match statement {
            Statement::VarDef(v) => {
                self.add_to_overlay(v.clone());
            }
            Statement::Cmd { blk, capture: None } => {
                for cmd in blk {
                    self.run_cmd_stmt(cmd.clone(), None)?;
                }
            }
            Statement::Cmd {
                blk,
                capture: Some(var),
            } => {
                let mut output = Vec::new();
                for cmd in blk {
                    self.run_cmd_stmt(cmd.clone(), Some(&mut output))?;
                }
                self.set_value(*var, Value::Bytes(Rc::new(output)))?;
            }
            Statement::Expr(e) => {
                self.eval_expr(&e)?;
            }
            Statement::Assign { lhs, rhs } => {
                let value = self.eval_expr(rhs)?;
                self.assign(lhs, value)?;
            }
            Statement::Branch(b) => self.run_branch(b)?,
        }
        Ok(StatementExec::NoAction)
    }

    fn run_branch(&mut self, branch: &cow_ast::Branch<'input>) -> RuntimeResult<()> {
        match branch {
            cow_ast::Branch::If(_) => todo!(),
            cow_ast::Branch::Loop(block) => {
                self.enter_overlay(Vec::new());
                'outer: loop {
                    for b in block {
                        match self.run_statement(b)? {
                            StatementExec::Break(_) => break 'outer,
                            StatementExec::Return(_) => todo!(),
                            StatementExec::NoAction => (),
                        }
                    }
                }
                self.overlays.pop();
            }
        }

        Ok(())
    }

    fn assign(
        &mut self,
        expr: &cow_ast::Expression<'input>,
        value: Gc<Value>,
    ) -> RuntimeResult<()> {
        match expr {
            cow_ast::Expression::Variable(name) => self.assign_var(*name, value),
            cow_ast::Expression::Call { .. } => todo!(),
            cow_ast::Expression::Method { .. } => todo!(),
            cow_ast::Expression::Unwrap(_) => todo!(),
            cow_ast::Expression::Cond { .. } => todo!(),
            cow_ast::Expression::Value(_)
            | cow_ast::Expression::SubShell(_)
            | cow_ast::Expression::Interpolated(_)
            | cow_ast::Expression::FuncDef { .. } => Err(RuntimeError::Unasignable),
        }
    }

    fn assign_var(&mut self, var: Spur, value: Gc<Value>) -> RuntimeResult<()> {
        for ov in self.overlays.iter_mut().rev() {
            match ov.values.get_mut(&var) {
                Some(v) => {
                    *v = value;
                    return Ok(());
                }
                None if ov.definitions.contains_key(&var) => {
                    ov.values.insert(var, value);
                    return Ok(());
                }
                None => (),
            }
        }

        Err(RuntimeError::Undefined(
            self.shell_ctx
                .rodeo
                .try_resolve(&var)
                .unwrap_or("<unkown>")
                .to_owned(),
        ))
    }

    pub fn run_script(&mut self, script: &[Statement<'input>]) -> RuntimeResult<()> {
        for stmt in script {
            self.run_statement(stmt)?;
        }

        Ok(())
    }
}
