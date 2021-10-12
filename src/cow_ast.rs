use crate::{lexer, rsh, ShellContext};
use lasso::Spur;
use once_cell::sync::Lazy;
use regex::Regex;
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

fn cow_to_owned(cow: CowStr<'_>) -> CowStr<'static> {
    match cow {
        Cow::Borrowed(b) => Cow::Owned(b.to_owned()),
        Cow::Owned(o) => Cow::Owned(o),
    }
}

// TODO: better errors
#[derive(Debug, thiserror::Error)]
#[error("parse error during interpolation")]
pub struct InterpolationError;

pub type AstResult<T> = Result<T, InterpolationError>;

static INTERPOLATION_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"\$[a-zA-Z0-9_]+|\$\{[^{}]*\}").unwrap());

impl StringPart<'static> {
    fn interpolate_owned(s: String, ctx: &mut ShellContext) -> AstResult<Vec<Self>> {
        let mut idx = 0;
        let mut interpolation = Vec::new();

        for mtch in INTERPOLATION_REGEX.find_iter(&s) {
            if mtch.start() != idx {
                interpolation.push(Self::Text(Cow::Owned(String::from(&s[idx..mtch.start()]))));
            }
            idx = mtch.end();
            let match_expr = &mtch.as_str()[1..];
            if match_expr.starts_with("{") {
                let input = match_expr.trim_start_matches('{').trim_end_matches('}');
                let expr = rsh::StrongExpressionParser::new()
                    .parse(ctx, input, lexer::lexer(&input))
                    .map_err(|_| InterpolationError)?;
                interpolation.push(Self::Expression(Expression::from_ast(expr, ctx)?.owned()));
            } else {
                interpolation.push(Self::Variable(ctx.rodeo.get_or_intern(&mtch.as_str()[1..])));
            }
        }
        if idx < s.len() {
            interpolation.push(Self::Text(Cow::Owned(String::from(&s[idx..]))))
        }

        Ok(interpolation)
    }
}

impl<'input> StringPart<'input> {
    pub fn interpolate(s: Cow<'input, str>, ctx: &mut ShellContext) -> AstResult<Vec<Self>> {
        match s {
            Cow::Borrowed(b) => StringPart::interpolate_borrowed(b, ctx),
            Cow::Owned(o) => StringPart::interpolate_owned(o, ctx),
        }
    }

    fn interpolate_borrowed(s: &'input str, ctx: &mut ShellContext) -> AstResult<Vec<Self>> {
        let mut idx = 0;
        let mut interpolation = Vec::new();

        for mtch in INTERPOLATION_REGEX.find_iter(&s) {
            if mtch.start() != idx {
                interpolation.push(Self::Text(Cow::Borrowed(&s[idx..mtch.start()])));
            }
            idx = mtch.end();
            let match_expr = &mtch.as_str()[1..];
            if match_expr.starts_with("{") {
                let input = match_expr.trim_start_matches('{').trim_end_matches('}');
                let expr = rsh::StrongExpressionParser::new()
                    .parse(ctx, input, lexer::lexer(&input))
                    .map_err(|_| InterpolationError)?;
                interpolation.push(Self::Expression(Expression::from_ast(expr, ctx)?));
            } else {
                interpolation.push(Self::Variable(ctx.rodeo.get_or_intern(&mtch.as_str()[1..])));
            }
        }
        if idx < s.len() {
            interpolation.push(Self::Text(Cow::Borrowed(&s[idx..])))
        }

        Ok(interpolation)
    }
}

fn convert_vec<I, O, F>(i: Vec<I>, f: F) -> Vec<O>
where
    F: Fn(I) -> O,
{
    i.into_iter().map(f).collect()
}

fn try_convert_vec<I, O, F>(i: Vec<I>, f: F) -> AstResult<Vec<O>>
where
    F: FnMut(I) -> AstResult<O>,
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

    pub fn from_ast(v: ast::Command<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        Ok(Self {
            name: Expression::from_ast(v.name, sh_ctx)?,
            args: try_convert_vec(v.args, |e| Expression::from_ast(e, sh_ctx))?,
            redirections: try_convert_vec(v.redirections, |(v, e)| {
                Ok((v, Expression::from_ast(e, sh_ctx)?))
            })?,
        })
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

    pub fn from_ast(v: ast::Pipeline<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        Ok(Self {
            commands: try_convert_vec(v.commands, |c| Command::from_ast(c, sh_ctx))?,
        })
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

    pub fn from_ast(v: ast::CommandChain<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        match v {
            ast::CommandChain::Or(a, b) => {
                Ok(Self::Or(a.into(), Box::new(Self::from_ast(*b, sh_ctx)?)))
            }
            ast::CommandChain::And(a, b) => {
                Ok(Self::And(a.into(), Box::new(Self::from_ast(*b, sh_ctx)?)))
            }
            ast::CommandChain::Pipeline(p) => Ok(Self::Pipeline(Pipeline::from_ast(p, sh_ctx)?)),
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

    pub fn from_ast(v: ast::VariableDefinition<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        Ok(Self {
            name: v.name,
            expr: Expression::from_ast(v.expr, sh_ctx)?,
            ty: v.ty,
        })
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

    pub fn from_ast(v: ast::CommandContext<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        Ok(Self {
            commands: try_convert_vec(v.commands, |c| CommandChain::from_ast(c, sh_ctx))?,
            variables: try_convert_vec(v.variables, |v| VariableDefinition::from_ast(v, sh_ctx))?,
        })
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

    pub fn from_ast(v: ast::CommandStatement<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        match v {
            ast::CommandStatement::Definitions(v) => {
                Ok(Self::Definitions(try_convert_vec(v, |d| {
                    VariableDefinition::from_ast(d, sh_ctx)
                })?))
            }
            ast::CommandStatement::Commands(c) => {
                Ok(Self::Commands(CommandContext::from_ast(c, sh_ctx)?))
            }
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
        capture: Option<Spur>,
    },
    #[serde(borrow)]
    Expr(Expression<'input>),
}

impl<'a> Statement<'a> {
    pub fn owned<'b>(self) -> Statement<'b> {
        match self {
            Statement::VarDef(v) => Statement::VarDef(v.owned()),
            Statement::Cmd { blk, capture } => Statement::Cmd {
                capture,
                blk: convert_vec(blk, |c| c.owned()),
            },
            Statement::Expr(e) => Statement::Expr(e.owned()),
        }
    }

    pub fn from_ast(v: ast::Statement<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        match v {
            ast::Statement::VarDef(v) => Ok(Self::VarDef(VariableDefinition::from_ast(v, sh_ctx)?)),
            ast::Statement::Cmd { blk, capture } => Ok(Self::Cmd {
                blk: try_convert_vec(blk, |b| CommandStatement::from_ast(b, sh_ctx))?,
                capture,
            }),
            ast::Statement::Expr(e) => Ok(Self::Expr(Expression::from_ast(e, sh_ctx)?)),
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

impl<'input> Value<'input> {
    pub fn owned<'b>(self) -> Value<'b> {
        match self {
            Value::String(s) => Value::String(cow_to_owned(s)),
            Value::Int(i) => Value::Int(i),
            Value::List(l) => Value::List(convert_vec(l, |e| e.owned())),
        }
    }

    pub fn from_ast(v: ast::Value<'input>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        match v {
            ast::Value::String(s) => Ok(Self::String(s)),
            ast::Value::Int(i) => Ok(Self::Int(i)),
            ast::Value::List(l) => Ok(Self::List(try_convert_vec(l, |v| {
                Expression::from_ast(v, sh_ctx)
            })?)),
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
    FuncDef {
        args: Vec<(Spur, Type)>,
        ret: Type,
        body: Vec<Statement<'input>>,
    },
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
            Expression::FuncDef { args, ret, body } => Expression::FuncDef {
                args,
                ret,
                body: convert_vec(body, |s| s.owned()),
            },
        }
    }
}

impl<'a> Expression<'a> {
    pub fn from_ast(v: ast::Expression<'a>, sh_ctx: &mut ShellContext) -> AstResult<Self> {
        match v {
            ast::Expression::Value(v) => Ok(Self::Value(Value::from_ast(v, sh_ctx)?)),
            ast::Expression::Call { function, args } => Ok(Self::Call {
                function: Box::new(Expression::from_ast(*function, sh_ctx)?),
                args: try_convert_vec(args, |e| Expression::from_ast(e, sh_ctx))?,
            }),
            ast::Expression::Method { value, name, args } => Ok(Self::Method {
                value: Box::new(Expression::from_ast(*value, sh_ctx)?),
                name,
                args: try_convert_vec(args, |e| Expression::from_ast(e, sh_ctx))?,
            }),
            ast::Expression::Interpolated(p) => {
                Ok(Self::Interpolated(StringPart::interpolate(p, sh_ctx)?))
            }
            ast::Expression::SubShell(c) => Ok(Self::SubShell(Box::new(CommandContext::from_ast(
                *c, sh_ctx,
            )?))),
            ast::Expression::Variable(v) => Ok(Self::Variable(v)),
            ast::Expression::FuncDef { args, ret, body } => Ok(Self::FuncDef {
                args,
                ret,
                body: try_convert_vec(body, |s| Statement::from_ast(s, sh_ctx))?,
            }),
        }
    }
}
