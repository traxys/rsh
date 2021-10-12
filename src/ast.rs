use gc::{Finalize, Trace};
use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::borrow::Cow;

#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub enum RedirectionType {
    In,
    Out,
    Append,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Command<'input> {
    #[serde(borrow)]
    pub name: Expression<'input>,
    #[serde(borrow)]
    pub args: Vec<Expression<'input>>,
    #[serde(borrow)]
    pub redirections: Vec<(RedirectionType, Expression<'input>)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pipeline<'input> {
    #[serde(borrow)]
    pub commands: Vec<Command<'input>>,
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

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Type {
    Dynamic,
    Int,
    String,
    Bytes,
    Private,
    Unit,
    Function { ret: Box<Type>, args: Vec<Type> },
    List(Box<Type>),
    Iterator(Box<Type>),
    Option(Box<Type>),
}

#[derive(PartialEq, Eq)]
pub(crate) enum TypeCheck {
    Compatible,
    Incompatible,
    Runtime,
}

impl Type {
    // Can you assign a expr_ty to self ?
    pub(crate) fn is_compatible(&self, expr_ty: &Type) -> TypeCheck {
        match (self, expr_ty) {
            (Self::Dynamic, _) => TypeCheck::Compatible,
            (_, Self::Dynamic) => TypeCheck::Runtime,
            (Self::Int, Self::Int) => TypeCheck::Compatible,
            (Self::String | Self::Bytes, Self::String | Self::Bytes) => TypeCheck::Compatible,
            (Self::Function { .. }, Self::Function { .. }) => TypeCheck::Compatible,
            (Self::Unit, Self::Unit) => TypeCheck::Compatible,
            (Self::List(s), Self::List(e)) => s.is_compatible(e),
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
            Type::Unit => write!(f, "()"),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VariableDefinition<'input> {
    pub name: Spur,
    #[serde(borrow)]
    pub expr: Expression<'input>,
    pub ty: Type,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommandContext<'input> {
    #[serde(borrow)]
    pub commands: Vec<CommandChain<'input>>,
    #[serde(borrow)]
    pub variables: Vec<VariableDefinition<'input>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CommandStatement<'input> {
    #[serde(borrow)]
    Definitions(Vec<VariableDefinition<'input>>),
    #[serde(borrow)]
    Commands(CommandContext<'input>),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Statement<'input> {
    #[serde(borrow)]
    VarDef(VariableDefinition<'input>),
    Cmd {
        #[serde(borrow)]
        blk: Vec<CommandStatement<'input>>,
        capture: Option<Spur>,
    },
    #[serde(borrow)]
    Expr(Expression<'input>),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Value<'input> {
    #[serde(borrow)]
    String(Cow<'input, str>),
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
pub enum Expression<'input> {
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
    Interpolated(Cow<'input, str>),
    SubShell(Box<CommandContext<'input>>),
    Variable(Spur),
    FuncDef {
        args: Vec<(Spur, Type)>,
        ret: Type,
        body: Vec<Statement<'input>>,
    },
    #[serde(borrow)]
    Unwrap(Box<Expression<'input>>),
}
