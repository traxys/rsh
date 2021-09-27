use lasso::Spur;
use serde::{Deserialize, Serialize};
use std::borrow::Cow;

use crate::ast;

type CowStr<'a> = Cow<'a, str>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StringPart<'input> {
    #[serde(borrow)]
    Text(CowStr<'input>),
    Variable(Spur),
    Expression(Expression<'input>),
}

impl<'a> From<ast::StringPart<'a>> for StringPart<'a> {
    fn from(v: ast::StringPart<'a>) -> Self {
        match v {
            ast::StringPart::Text(t) => Self::Text(CowStr::Borrowed(t)),
            ast::StringPart::Variable(v) => Self::Variable(v),
            ast::StringPart::Expression(e) => Self::Expression(e.into()),
        }
    }
}

pub type RedirectionType = ast::RedirectionType;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Command<'input> {
    #[serde(borrow)]
    pub name: Expression<'input>,
    #[serde(borrow)]
    pub args: Vec<Expression<'input>>,
    #[serde(borrow)]
    pub redirections: Vec<(RedirectionType, Expression<'input>)>,
}

impl<'a> From<ast::Command<'a>> for Command<'a> {
    fn from(v: ast::Command<'a>) -> Self {
        Self {
            name: v.name.into(),
            args: v.args.into_iter().map(From::from).collect(),
            redirections: v
                .redirections
                .into_iter()
                .map(|(v, e)| (v, e.into()))
                .collect(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pipeline<'input> {
    #[serde(borrow)]
    pub commands: Vec<Command<'input>>,
}

impl<'a> From<ast::Pipeline<'a>> for Pipeline<'a> {
    fn from(v: ast::Pipeline<'a>) -> Self {
        Self {
            commands: v.commands.into_iter().map(From::from).collect(),
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

impl<'a> From<ast::ChainPart<'a>> for ChainPart<'a> {
    fn from(v: ast::ChainPart<'a>) -> Self {
        match v {
            ast::ChainPart::Pipeline(_) => todo!(),
            ast::ChainPart::Chain(_) => todo!(),
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

impl<'a> From<ast::CommandChain<'a>> for CommandChain<'a> {
    fn from(v: ast::CommandChain<'a>) -> Self {
        match v {
            ast::CommandChain::Or(a, b) => Self::Or(a.into(), Box::new((*b).into())),
            ast::CommandChain::And(a, b) => Self::And(a.into(), Box::new((*b).into())),
            ast::CommandChain::Pipeline(p) => Self::Pipeline(p.into()),
        }
    }
}

pub type Type = ast::Type;

pub(crate) type TypeCheck = ast::TypeCheck;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VariableDefinition<'input> {
    pub name: Spur,
    #[serde(borrow)]
    pub expr: Expression<'input>,
    pub ty: Type,
}

impl<'a> From<ast::VariableDefinition<'a>> for VariableDefinition<'a> {
    fn from(v: ast::VariableDefinition<'a>) -> Self {
        Self {
            name: v.name,
            expr: v.expr.into(),
            ty: v.ty,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CommandContext<'input> {
    #[serde(borrow)]
    pub commands: Vec<CommandChain<'input>>,
    #[serde(borrow)]
    pub variables: Vec<VariableDefinition<'input>>,
}

impl<'a> From<ast::CommandContext<'a>> for CommandContext<'a> {
    fn from(v: ast::CommandContext<'a>) -> Self {
        Self {
            commands: v.commands.into_iter().map(From::from).collect(),
            variables: v.variables.into_iter().map(From::from).collect(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CommandStatement<'input> {
    #[serde(borrow)]
    Definitions(Vec<VariableDefinition<'input>>),
    #[serde(borrow)]
    Commands(CommandContext<'input>),
}

impl<'a> From<ast::CommandStatement<'a>> for CommandStatement<'a> {
    fn from(v: ast::CommandStatement<'a>) -> Self {
        match v {
            ast::CommandStatement::Definitions(v) => {
                Self::Definitions(v.into_iter().map(Into::into).collect())
            }
            ast::CommandStatement::Commands(c) => Self::Commands(c.into()),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Statement<'input> {
    #[serde(borrow)]
    VarDef(VariableDefinition<'input>),
    Cmd {
        #[serde(borrow)]
        blk: Vec<CommandStatement<'input>>,
        capture: bool,
    },
}

impl<'a> From<ast::Statement<'a>> for Statement<'a> {
    fn from(v: ast::Statement<'a>) -> Self {
        match v {
            ast::Statement::VarDef(v) => Self::VarDef(v.into()),
            ast::Statement::Cmd { blk, capture } => Self::Cmd {
                blk: blk.into_iter().map(Into::into).collect(),
                capture,
            },
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Value<'input> {
    #[serde(borrow)]
    String(CowStr<'input>),
    Int(i64),
    List(Vec<Expression<'input>>),
}

impl<'a> From<ast::Value<'a>> for Value<'a> {
    fn from(v: ast::Value<'a>) -> Self {
        match v {
            ast::Value::String(s) => Self::String(CowStr::Borrowed(s)),
            ast::Value::Int(i) => Self::Int(i),
            ast::Value::List(l) => Self::List(l.into_iter().map(Into::into).collect()),
        }
    }
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
    Interpolated(Vec<StringPart<'input>>),
    SubShell(Box<CommandContext<'input>>),
    Variable(Spur),
}

impl<'a> From<ast::Expression<'a>> for Expression<'a> {
    fn from(v: ast::Expression<'a>) -> Self {
        match v {
            ast::Expression::Value(v) => Self::Value(v.into()),
            ast::Expression::Call { function, args } => Self::Call {
                function: Box::new((*function).into()),
                args: args.into_iter().map(Into::into).collect(),
            },
            ast::Expression::Method { value, name, args } => Self::Method {
                value: Box::new((*value).into()),
                name,
                args: args.into_iter().map(Into::into).collect(),
            },
            ast::Expression::Interpolated(p) => {
                Self::Interpolated(p.into_iter().map(Into::into).collect())
            }
            ast::Expression::SubShell(c) => Self::SubShell(Box::new((*c).into())),
            ast::Expression::Variable(v) => Self::Variable(v),
        }
    }
}
