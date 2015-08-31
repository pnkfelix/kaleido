```rust
use ast::{self, Expr};

use llvm::{self, Value};
use llvm::Compile; // provides `fn compile` and `fn get_type`

use std::borrow::{Cow};
use std::cell::RefCell;
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
    EmptyBody,
}

fn err<T>(kind: CodegenErrorKind) -> Result<T> {
    Err(error(kind))
}
fn error(kind: CodegenErrorKind) -> CodegenError {
    CodegenError { kind: kind }
}

type Builder<'c> = llvm::CSemiBox<'c, llvm::Builder>;
type Module<'c> = llvm::CSemiBox<'c, llvm::Module>;

pub struct ContextState<'c> {
    llvm_context: &'c llvm::Context,
    module: Module<'c>,
    builder: Builder<'c>,
}

impl<'c> ContextState<'c> {
    pub fn new(llvm_context: &'c llvm::Context, name: &str) -> ContextState<'c> {
        ContextState {
            llvm_context: llvm_context,
            module: llvm::Module::new(name, llvm_context),
            builder: llvm::Builder::new(llvm_context),
        }
    }
}

pub struct Context<'c> {
    llvm_context: &'c llvm::Context,
    module: &'c Module<'c>,
    builder: &'c Builder<'c>,
    named_values: RefCell<HashMap<String, &'c Value>>,
}

impl<'c> Context<'c> {
    pub fn from_context_state(ctxt: &'c ContextState<'c>) -> Context<'c> {
        Context {
            llvm_context: &ctxt.llvm_context,
            module: &ctxt.module,
            builder: &ctxt.builder,
            named_values: RefCell::new(HashMap::new()),
        }
    }
}

impl<'c> Context<'c> {
    fn get_type<T: Compile<'c>>(&self) -> &'c llvm::Type {
        <T as Compile>::get_type(self.llvm_context)
    }
    fn with_1_arg<F>(&self,
                     e1: &ast::Expr,
                     f: F) -> Result<&'c Value>
        where F: Fn(&'c Builder<'c>, &'c Value) -> &'c Value
    {
        let v1 = try!(e1.codegen(self));
        Ok(f(self.builder, v1))
    }

    fn with_2_args<F>(&self,
                      e1: &ast::Expr,
                      e2: &ast::Expr,
                      f: F) -> Result<&'c Value>
        where F: Fn(&'c Builder<'c>, &'c Value, &'c Value) -> &'c Value
    {
        let v1 = try!(e1.codegen(self));
        let v2 = try!(e2.codegen(self));
        Ok(f(self.builder, v1, v2))
    }
}

impl Expr {
    pub fn codegen<'c>(&self, ctxt: &Context<'c>) -> Result<&'c Value> {
        match *self {
            Expr::Number(n) => Ok(n.compile(ctxt.llvm_context)),
            Expr::Ident(ref s) => ctxt.named_values.borrow_mut().get(&*s.name)
                .map(|v|*v)
                .ok_or(error(CodegenErrorKind::LookupVarFailure(s.clone()))),
            Expr::Op(_) => panic!("operators are not really expressions"),
            Expr::Def(ref p, ref body) => codegen_def(p, body, ctxt),
            Expr::Extern(ref p) => codegen_extern(p, ctxt),
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
                    let t = ctxt.get_type::<f32>();
                    ctxt.with_2_args(e1, e2, |b, v1, v2| {
                        b.build_ui_to_fp(b.build_cmp(v1, v2, llvm::Predicate::LessThan),
                                         t)
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
                    // let actuals: Vec<_> =
                    //     try!(args.iter().map(|a|a.codegen(ctxt)).collect());
                    let mut actuals = Vec::new();
                    for a in args {
                        actuals.push(try!(a.codegen(ctxt)));
                    }
                    Ok(ctxt.builder.build_call(callee, &actuals[..]))
                }
                _ => unimplemented!(),
            }
        }
    }
}

impl ast::Proto {
    pub fn skeleton<'c>(&self, ctxt: &Context<'c>) -> &'c mut llvm::Function {
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

fn lookup_or_generate_function<'c>(p: &ast::Proto,
                                   ctxt: &Context<'c>) -> Result<&'c llvm::Function> {
    let arg_len = p.args.len();
    let f: &'c llvm::Function =
        match ctxt.module.get_function(&p.name.name) {
            None => p.skeleton(ctxt),
            Some(f) => f,
        };
    let actual_len = f.get_signature().num_params();
    if actual_len == arg_len {
        Ok(f)
    } else {
        err(CodegenErrorKind::ArgMismatch { expect: arg_len,
                                            actual: actual_len, })
    }
}

fn codegen_extern<'c>(p: &ast::Proto,
                      ctxt: &Context<'c>) -> Result<&'c Value> {
    Ok(try!(lookup_or_generate_function(p, ctxt)))
}

fn codegen_def<'c>(p: &ast::Proto,
                   body: &[Expr],
                   ctxt: &Context<'c>) -> Result<&'c Value> {
    let f = try!(lookup_or_generate_function(p, ctxt));
    let arg_len = p.args.len();

    // it would be nice to follow the tutorial's assertion that
    // f.empty() here (to ensure that it was not already defined).
    //
    // assert!(f.get_entry().is_none());
    //
    // but AFAICT, the functions we create start off with entries.

    let bb = f.append("entry");
    ctxt.builder.position_at_end(bb);
    ctxt.named_values.borrow_mut().clear();
    for i in 0..arg_len {
        let arg = &f[i];
        ctxt.named_values
            .borrow_mut()
            .insert(arg.get_name().unwrap().to_owned(), arg);
    }
    let mut ret_val = None;
    for b in body {
        ret_val = Some(try!(b.codegen(ctxt)));
    }

    match ret_val {
        Some(ret_val) => ctxt.builder.build_ret(ret_val),
        None => return err(CodegenErrorKind::EmptyBody),
    };

    Ok(f)
}

#[cfg(test)]
use inputs;

#[test]
fn dump_ir() {
    use llvm_sys;

    let llvm_context = llvm::Context::new();
    let ctxt = ContextState::new(&llvm_context, "kaleido jit");
    let ctxt = Context::from_context_state(&ctxt);

    // these are definitions so they are included in the dump.
    inputs::def_id().ast.codegen(&ctxt).unwrap();

    inputs::def_foo().ast.codegen(&ctxt).unwrap();

    inputs::def_discrim().ast.codegen(&ctxt).unwrap();
    inputs::def_quad_root_a().ast.codegen(&ctxt).unwrap();

    unsafe {
        let mref: llvm_sys::prelude::LLVMModuleRef = (*ctxt.module).as_ptr();
        llvm_sys::core::LLVMDumpModule(mref);
    }
}
```
