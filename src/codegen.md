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
    LookupFailure(ast::Ident),
}

type Builder<'c> = llvm::CSemiBox<'c, llvm::Builder>;

pub struct Context<'c> {
    llvm_context: &'c llvm::Context,
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
                .ok_or(CodegenError {
                    kind: CodegenErrorKind::LookupFailure(s.clone())
                }),
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
                _ => unimplemented!(),
            }
        }
    }
}
```
