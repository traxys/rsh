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

fn cow_to_owned(cow: CowStr<'_>) -> CowStr<'static> {
    match cow {
        Cow::Borrowed(b) => Cow::Owned(b.to_owned()),
        Cow::Owned(o) => Cow::Owned(o),
    }
}

fn convert_vec<I, O, F>(i: Vec<I>, f: F) -> Vec<O>
where
    F: Fn(I) -> O,
{
    i.into_iter().map(f).collect()
}

impl<'a> StringPart<'a> {
    pub fn owned<'b>(self) -> StringPart<'b> {
        match self {
            StringPart::Text(v) => StringPart::Text(cow_to_owned(v)),
            StringPart::Variable(v) => StringPart::Variable(v),
            StringPart::Expression(e) => StringPart::Expression(e.owned()),
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

impl<'a> Command<'a> {
    pub fn owned<'b>(self) -> Command<'b> {
        Command {
            name: self.name.owned(),
            args: convert_vec(self.args, |e| e.owned()),
            redirections: convert_vec(self.redirections, |(v, e)| (v, e.owned())),
        }
    }
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

impl<'a> Pipeline<'a> {
    pub fn owned<'b>(self) -> Pipeline<'b> {
        Pipeline {
            commands: convert_vec(self.commands, |e| e.owned()),
        }
    }
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

impl<'a> ChainPart<'a> {
    pub fn owned<'b>(self) -> ChainPart<'b> {
        match self {
            ChainPart::Pipeline(p) => ChainPart::Pipeline(p.owned()),
            ChainPart::Chain(c) => ChainPart::Chain(Box::new(c.owned())),
        }
    }
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

impl<'a> CommandChain<'a> {
    pub fn owned<'b>(self) -> CommandChain<'b> {
        match self {
            CommandChain::Or(p, r) => CommandChain::Or(p.owned(), Box::new(r.owned())),
            CommandChain::And(p, r) => CommandChain::And(p.owned(), Box::new(r.owned())),
            CommandChain::Pipeline(p) => CommandChain::Pipeline(p.owned()),
        }
    }
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

impl<'a> VariableDefinition<'a> {
    pub fn owned<'b>(self) -> VariableDefinition<'b> {
        VariableDefinition {
            name: self.name,
            ty: self.ty,
            expr: self.expr.owned(),
        }
    }
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

impl<'a> CommandContext<'a> {
    pub fn owned<'b>(self) -> CommandContext<'b> {
        CommandContext {
            commands: convert_vec(self.commands, |c| c.owned()),
            variables: convert_vec(self.variables, |v| v.owned()),
        }
    }
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

impl<'a> CommandStatement<'a> {
    pub fn owned<'b>(self) -> CommandStatement<'b> {
        match self {
            CommandStatement::Definitions(d) => {
                CommandStatement::Definitions(convert_vec(d, |v| v.owned()))
            }
            CommandStatement::Commands(c) => CommandStatement::Commands(c.owned()),
        }
    }
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

impl<'a> Statement<'a> {
    pub fn owned<'b>(self) -> Statement<'b> {
        match self {
            Statement::VarDef(v) => Statement::VarDef(v.owned()),
            Statement::Cmd { blk, capture } => Statement::Cmd {
                capture,
                blk: convert_vec(blk, |c| c.owned()),
            },
        }
    }
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

    pub fn owned<'b>(self) -> Value<'b> {
        match self {
            Value::String(s) => Value::String(cow_to_owned(s)),
            Value::Int(i) => Value::Int(i),
            Value::List(l) => Value::List(convert_vec(l, |e| e.owned())),
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

impl<'a> Expression<'a> {
    pub fn owned<'b>(self) -> Expression<'b> {
        match self {
            Expression::Value(v) => Expression::Value(v.owned()),
            Expression::Call { function, args } => Expression::Call {
                function: Box::new(function.owned()),
                args: convert_vec(args, |a| a.owned()),
            },
            Expression::Method { value, name, args } => Expression::Method {
                value: Box::new(value.owned()),
                args: convert_vec(args, |arg| arg.owned()),
                name,
            },
            Expression::Interpolated(i) => Expression::Interpolated(convert_vec(i, |p| p.owned())),
            Expression::SubShell(ctx) => Expression::SubShell(Box::new(ctx.owned())),
            Expression::Variable(v) => Expression::Variable(v),
        }
    }
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
