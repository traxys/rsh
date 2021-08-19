use crate::Type;

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
    ($(fn $name:ident($($arg:ident),*) -> $ret:ident);* $(;)?) => {
        vec![$(
            BuiltinFunction {
                name: stringify!($name),
                ret: Type::$ret,
                args: vec![$(Type::$arg,)*],
            }
        ),*]
    };
}

pub(crate) fn builtins() -> Vec<BuiltinFunction> {
    builtins_defs!(
        fn s(Dynamic) -> String;
        fn env(String, String) -> String;
        fn json(Dynamic) -> String;
    )
}
