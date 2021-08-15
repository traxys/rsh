use crate::{ShellContext, Type, TypeCheck, VariableDefinition};
use lasso::Spur;
use std::collections::HashMap;

pub type TypeCheckResult<T = ()> = Result<T, Vec<TypeError>>;

#[derive(Debug, Copy, Clone, thiserror::Error)]
pub enum TypeError {
    #[error("type mismatch: expected {} got {}", expected, got)]
    Mismatch { expected: Type, got: Type },
    #[error("undefined identifier")]
    Undefined,
}

fn root_types(shell_ctx: &mut ShellContext) -> HashMap<Spur, Type> {
    let mut tys = HashMap::new();
    tys.insert(shell_ctx.rodeo.get_or_intern_static("exit"), Type::Int);
    tys
}

pub struct TypeCheckerCtx<'ctx> {
    pub shell_ctx: &'ctx mut ShellContext,
    overlays: Vec<Overlay>,
}

struct Overlay {
    types: HashMap<Spur, Type>,
}

fn merge_errors<T, U>(a: TypeCheckResult<T>, b: TypeCheckResult<U>) -> TypeCheckResult<(T, U)> {
    match b {
        Ok(u) => match a {
            Err(e) => Err(e),
            Ok(t) => Ok((t, u)),
        },
        Err(mut errs) => match a {
            Ok(_) => Err(errs),
            Err(mut e) => {
                e.append(&mut errs);
                Err(e)
            }
        },
    }
}

fn merge_unit(a: TypeCheckResult, b: TypeCheckResult) -> TypeCheckResult {
    match merge_errors(a, b) {
        Err(e) => Err(e),
        Ok(_) => Ok(()),
    }
}

fn fold_unit<I, T, F>(iter: I, mut f: F) -> TypeCheckResult
where
    I: Iterator<Item = T>,
    F: FnMut(T) -> TypeCheckResult,
{
    iter.fold(Ok(()), |result, item| merge_unit(result, f(item)))
}

fn fold_errors<I, T, F, R>(iter: I, mut f: F) -> TypeCheckResult<Vec<R>>
where
    I: Iterator<Item = T>,
    F: FnMut(T) -> TypeCheckResult<R>,
{
    iter.fold(Ok(Vec::new()), |result, item| {
        match merge_errors(result, f(item)) {
            Ok((mut r, new)) => {
                r.push(new);
                Ok(r)
            }
            Err(e) => Err(e),
        }
    })
}

impl<'ctx> TypeCheckerCtx<'ctx> {
    pub fn new(shell_ctx: &'ctx mut ShellContext) -> Self {
        Self {
            overlays: vec![Overlay {
                types: root_types(shell_ctx),
            }],
            shell_ctx,
        }
    }

    fn enter_overlay(&mut self, definitions: &[VariableDefinition<'_>]) {
        self.overlays.push(Overlay {
            types: definitions.iter().map(|def| (def.name, def.ty)).collect(),
        })
    }

    pub fn check_cmd_ctx(&mut self, cmd_ctx: &super::CommandContext<'_>) -> TypeCheckResult {
        self.enter_overlay(&cmd_ctx.variables);

        merge_unit(
            self.check_definitions(&cmd_ctx.variables),
            fold_unit(cmd_ctx.commands.iter(), |chain| self.check_chain(chain)),
        )?;

        self.overlays.pop();

        Ok(())
    }

    fn check_definitions(&mut self, definitions: &[VariableDefinition<'_>]) -> TypeCheckResult {
        fold_unit(definitions.iter(), |def| self.check_definition(def))
    }

    fn check_definition(&mut self, def: &VariableDefinition) -> TypeCheckResult {
        let ty = self.check_expression(&def.expr)?;
        match def.ty.is_compatible(ty) {
            TypeCheck::Compatible | TypeCheck::Runtime => Ok(()),
            TypeCheck::Incompatible => Err(vec![TypeError::Mismatch {
                expected: def.ty,
                got: ty,
            }]),
        }
    }

    fn check_chain(&mut self, chain: &super::CommandChain) -> TypeCheckResult {
        match chain {
            crate::CommandChain::Or(c, rest) | crate::CommandChain::And(c, rest) => {
                merge_unit(self.check_chain_part(c), self.check_chain(rest))
            }
            crate::CommandChain::Pipeline(p) => self.check_pipeline(p),
        }
    }

    fn check_chain_part(&mut self, chain_part: &super::ChainPart) -> TypeCheckResult {
        match chain_part {
            crate::ChainPart::Pipeline(p) => self.check_pipeline(p),
            crate::ChainPart::Chain(c) => self.check_chain(c),
        }
    }

    fn check_pipeline(&mut self, pipeline: &super::Pipeline) -> TypeCheckResult {
        fold_unit(pipeline.commands.iter(), |cmd| self.check_command(cmd))
    }

    fn check_command(&mut self, cmd: &super::Command) -> TypeCheckResult {
        merge_unit(
            self.check_expression(&cmd.name).map(|_| ()),
            merge_unit(
                fold_unit(cmd.args.iter(), |expr| {
                    self.check_expression(expr).map(|_| ())
                }),
                fold_unit(cmd.redirections.iter().map(|(_, expr)| expr), |expr| {
                    self.check_expression(expr).map(|_| ())
                }),
            ),
        )
    }

    fn check_expression(&mut self, expr: &super::Expression) -> TypeCheckResult<Type> {
        match expr {
            crate::Expression::Value(v) => Ok(v.ty()),
            crate::Expression::Call { function, args } => {
                let (_func_ty, _args_ty) = merge_errors(
                    self.check_expression(function),
                    fold_errors(args.iter(), |expr| self.check_expression(expr)),
                )?;
                todo!("func type")
            }
            crate::Expression::Interpolated(i) => {
                self.check_interpolated(i)?;
                Ok(Type::String)
            }
            crate::Expression::SubShell(subshell) => {
                self.check_cmd_ctx(subshell)?;
                Ok(Type::Bytes)
            }
            crate::Expression::Variable(v) => self
                .resolve(*v)
                .map(Ok)
                .unwrap_or_else(|| Err(vec![TypeError::Undefined])),
        }
    }

    fn check_interpolated(&mut self, _: &[super::StringPart]) -> TypeCheckResult {
        Ok(())
    }

    fn resolve(&self, name: Spur) -> Option<Type> {
        self.overlays
            .iter()
            .rev()
            .find_map(|overlay| overlay.types.get(&name).copied())
    }
}
