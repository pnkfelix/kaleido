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
                    let v1 = try!(e1.codegen(ctxt));
                    Ok(ctxt.builder.build_neg(v1))
                }
                [Expr::Op('!'), ref e1] => {
                    let v1 = try!(e1.codegen(ctxt));
                    Ok(ctxt.builder.build_not(v1))
                }
                [Expr::Op('+'), ref e1, ref e2] => {
                    let v1 = try!(e1.codegen(ctxt));
                    let v2 = try!(e2.codegen(ctxt));
                    Ok(ctxt.builder.build_add(v1, v2))
                }
                [Expr::Op('-'), ref e1, ref e2] => {
                    let v1 = try!(e1.codegen(ctxt));
                    let v2 = try!(e2.codegen(ctxt));
                    Ok(ctxt.builder.build_sub(v1, v2))
                }
                [Expr::Op('*'), ref e1, ref e2] => {
                    let v1 = try!(e1.codegen(ctxt));
                    let v2 = try!(e2.codegen(ctxt));
                    Ok(ctxt.builder.build_mul(v1, v2))
                }
                [Expr::Op('/'), ref e1, ref e2] => {
                    let v1 = try!(e1.codegen(ctxt));
                    let v2 = try!(e2.codegen(ctxt));
                    Ok(ctxt.builder.build_mul(v1, v2))
                }
                [Expr::Op('&'), ref e1, ref e2] => {
                    let v1 = try!(e1.codegen(ctxt));
                    let v2 = try!(e2.codegen(ctxt));
                    Ok(ctxt.builder.build_and(v1, v2))
                }
                [Expr::Op('|'), ref e1, ref e2] => {
                    let v1 = try!(e1.codegen(ctxt));
                    let v2 = try!(e2.codegen(ctxt));
                    Ok(ctxt.builder.build_or(v1, v2))
                }
                [Expr::Op('<'), ref e1, ref e2] => {
                    let v1 = try!(e1.codegen(ctxt));
                    let v2 = try!(e2.codegen(ctxt));
                    let vcmp = ctxt.builder.build_cmp(v1, v2, llvm::Predicate::LessThan);
                    Ok(vcmp)
                }
                _ => unimplemented!(),
            }
        }
    }
}
```
