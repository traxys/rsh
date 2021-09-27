use crate::ast::{Type, Type::*};

pub(crate) struct BuiltinFunction {
    pub name: &'static str,
    ret: Type,
    args: Vec<Type>,
}

impl BuiltinFunction {
    pub(crate) fn ty(&self) -> Type {
        Type::Function {
            ret: Box::new(self.ret.clone()),
            args: self.args.clone(),
        }
    }
}

macro_rules! builtins_defs {
    ($(fn $name:ident($($arg:expr),*) -> $ret:expr);* $(;)?) => {
        vec![$(
            BuiltinFunction {
                name: stringify!($name),
                ret: $ret,
                args: vec![$($arg,)*],
            }
        ),*]
    };
}

pub(crate) fn builtins() -> Vec<BuiltinFunction> {
    builtins_defs!(
        fn s(Dynamic) -> String;
        fn env(String, String) -> String;
        fn json(Dynamic) -> String;
        fn range(Int,Int) -> Iterator(Box::new(Int));
        fn next(Iterator(Box::new(Dynamic))) -> Option(Box::new(Dynamic));
    )
}
