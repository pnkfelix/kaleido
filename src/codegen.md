```rust
use ast::{self, Expr};

use llvm::{self, Value};
use llvm::Compile; // provides `fn compile` and `fn get_type`
use std::borrow::{Cow};
use std::collections::HashMap;
use std::result::Result as StdResult;

pub type Result<T> = StdResult<T, CodegenError>;

#[derive(PartialEq, Debug)]
pub struct CodegenError {
    kind: CodegenErrorKind,
}

#[derive(PartialEq, Debug)]
pub enum CodegenErrorKind {
    Generic(Cow<'static, str>),
    LookupVarFailure(ast::Ident),
    LookupOpFailure(ast::Ident),
    ArgMismatch { expect: usize, actual: usize },
}

fn err<T>(kind: CodegenErrorKind) -> Result<T> {
    Err(error(kind))
}
fn error(kind: CodegenErrorKind) -> CodegenError {
    CodegenError { kind: kind }
}

type Builder<'c> = llvm::CSemiBox<'c, llvm::Builder>;
type Module<'c> = llvm::CSemiBox<'c, llvm::Module>;

pub struct Context<'c> {
    llvm_context: &'c llvm::Context,
    module: Module<'c>,
    builder: Builder<'c>,
    named_values: HashMap<String, &'c Value>,
}

impl<'c> Context<'c> {
    fn get_type<T: Compile<'c>>(&'c self) -> &'c llvm::Type {
        <T as Compile>::get_type(self.llvm_context)
    }
    fn with_1_arg<F>(&'c self, e1: &ast::Expr, f: F) -> Result<&'c Value>
        where F: Fn(&'c Builder<'c>, &'c Value) -> &'c Value
    {
        let v1 = try!(e1.codegen(self));
        Ok(f(&self.builder, v1))
    }

    fn with_2_args<F>(&'c self, e1: &ast::Expr, e2: &ast::Expr, f: F) -> Result<&'c Value>
        where F: Fn(&'c Builder<'c>, &'c Value, &'c Value) -> &'c Value
    {
        let v1 = try!(e1.codegen(self));
        let v2 = try!(e2.codegen(self));
        Ok(f(&self.builder, v1, v2))
    }
}

impl Expr {
    pub fn codegen<'c>(&self, ctxt: &'c Context<'c>) -> Result<&'c Value> {
        match *self {
            Expr::Number(n) => Ok(n.compile(ctxt.llvm_context)),
            Expr::Ident(ref s) => ctxt.named_values.get(&*s.name)
                .map(|v|*v)
                .ok_or(error(CodegenErrorKind::LookupVarFailure(s.clone()))),
            Expr::Op(_) => panic!("operators are not really expressions"),
            Expr::Def(ref _p, ref _body) => unimplemented!(),
            Expr::Extern(ref _p) => unimplemented!(),

            Expr::Combine(ref exprs) => match &exprs[..] {
                [Expr::Op('-'), ref e1] => {
                    ctxt.with_1_arg(e1, |b, v1| b.build_neg(v1))
                }
                [Expr::Op('!'), ref e1] => {
                    ctxt.with_1_arg(e1, |b, v1| b.build_not(v1))
                }
                [Expr::Op('+'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_add(v1, v2))
                }
                [Expr::Op('-'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_sub(v1, v2))
                }
                [Expr::Op('*'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_mul(v1, v2))
                }
                [Expr::Op('/'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_div(v1, v2))
                }
                [Expr::Op('&'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_and(v1, v2))
                }
                [Expr::Op('|'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_or(v1, v2))
                }
                [Expr::Op('<'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| {
                        b.build_ui_to_fp(b.build_cmp(v1, v2, llvm::Predicate::LessThan),
                                         ctxt.get_type::<f32>())
                    })
                }
                [Expr::Ident(ref s), args..] => {
                    let callee = match ctxt.module.get_function(&*s.name) {
                        Some(f) => f,
                        None => return err(CodegenErrorKind::LookupOpFailure(s.clone())),
                    };
                    let sig = callee.get_signature();
                    if sig.num_params() != args.len() {
                        return err(CodegenErrorKind::ArgMismatch {
                            expect: sig.num_params(),
                            actual: args.len() });
                    }
                    let actuals: Vec<_> =
                        try!(args.iter().map(|a|a.codegen(ctxt)).collect());
                    Ok(ctxt.builder.build_call(callee, &actuals[..]))
                }
                _ => unimplemented!(),
            }
        }
    }
}

impl ast::Proto {
    pub fn skeleton<'c>(&self, ctxt: &'c Context<'c>) -> &'c mut llvm::Function {
        let double_ty = f64::get_type(ctxt.llvm_context);
        let arg_len = self.args.len();
        let arg_tys: Vec<_> = (0..arg_len).map(|_| double_ty).collect();
        let sig = llvm::Type::new_function(double_ty, &arg_tys[..]);
        let f = ctxt.module.add_function(&self.name.name, sig);
        for i in 0..arg_len {
            f[i].set_name(&self.args[i].name);
        }
        f
    }
}
```
