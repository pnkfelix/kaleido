```rust
#![allow(unused_variables)]

use ast::{self, Expr};

use llvm::{self, Value, ToValue};
use llvm::Compile;

use llvm_sys;

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
    FunctionRedefinition,
    EmptyBody,
}

fn err<T>(kind: CodegenErrorKind) -> Result<T> {
    Err(error(kind))
}
fn error(kind: CodegenErrorKind) -> CodegenError {
    CodegenError { kind: kind }
}

pub struct Context<'c> {
    llvm_context: &'c llvm::Context<'c>,
    module: llvm::Module<'c>,
    builder: llvm::Builder<'c>,
    pub named_values: RefCell<HashMap<String, Value<'c>>>,
}

impl<'c> Context<'c> {
    pub fn new(llvm_context: &'c llvm::Context<'c>, name: &str) -> Context<'c> {
        Context {
            llvm_context: llvm_context,
            module: llvm::Module::new(name, llvm_context),
            builder: llvm::Builder::new(llvm_context),
            named_values: RefCell::new(HashMap::new()),
        }
    }
}

impl<'c> Context<'c> {
    fn with_1_arg<F>(&self,
                     e1: &ast::Expr,
                     f: F) -> Result<Value<'c>>
        where F: Fn(&llvm::Builder<'c>, Value<'c>) -> Value<'c>
    {
        let v1 = try!(e1.codegen(self));
        Ok(f(&self.builder, v1))
    }

    fn with_2_args<F>(&self,
                      e1: &ast::Expr,
                      e2: &ast::Expr,
                      f: F) -> Result<Value<'c>>
        where F: Fn(&llvm::Builder<'c>, Value<'c>, Value<'c>) -> Value<'c>
    {
        let v1 = try!(e1.codegen(self));
        let v2 = try!(e2.codegen(self));
        Ok(f(&self.builder, v1, v2))
    }
}

impl Expr {
    pub fn codegen<'c>(&self, ctxt: &Context<'c>) -> Result<Value<'c>> {
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
                    // https://github.com/TomBebbington/llvm-rs/issues/3
                    // `build_neg` will only work for integer inputs
                    // so we resort to `build_sub` instead.
                    ctxt.with_1_arg(e1, |b, v1| b.build_fsub(
                        (0.0).compile(ctxt.llvm_context),
                        v1,
                        None))
                }
                [Expr::Op('!'), ref e1] => {
                    ctxt.with_1_arg(e1, |b, v1| b.build_not(v1))
                }
                [Expr::Op('+'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_fadd(v1, v2, None))
                }
                [Expr::Op('-'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_fsub(v1, v2, None))
                }
                [Expr::Op('*'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_fmul(v1, v2, None))
                }
                [Expr::Op('/'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_fdiv(v1, v2, None))
                }
                [Expr::Op('&'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_and(v1, v2, None))
                }
                [Expr::Op('|'), ref e1, ref e2] => {
                    ctxt.with_2_args(e1, e2, |b, v1, v2| b.build_or(v1, v2, None))
                }
                [Expr::Op('<'), ref e1, ref e2] => {
                    let t: &llvm::Type = ctxt.llvm_context.get_type::<f32>();
                    ctxt.with_2_args(e1, e2, |b, v1, v2| {
                        b.build_ui_to_fp(
                            b.build_fcmp(v1, v2, llvm_sys::LLVMRealPredicate::LLVMRealOLT),
                            t)
                    })
                }
                [Expr::Ident(ref s), args..] => {
                    let callee = match ctxt.module.get_function(&*s.name) {
                        Some(f) => f,
                        None => return err(CodegenErrorKind::LookupOpFailure(s.clone())),
                    };
                    let num_params = callee.num_params();
                    if num_params != args.len() {
                        return err(CodegenErrorKind::ArgMismatch {
                            expect: num_params,
                            actual: args.len() });
                    }
                    // let actuals: Vec<_> =
                    //     try!(args.iter().map(|a|a.codegen(ctxt)).collect());
                    let mut actuals = Vec::new();
                    for a in args {
                        actuals.push(try!(a.codegen(ctxt)));
                    }
                    Ok(ctxt.builder.build_call(callee, &mut actuals[..], None).to_value())
                }
                _ => unimplemented!(),
            }
        }
    }
}

impl ast::Proto {
    pub fn skeleton<'c>(&self, ctxt: &Context<'c>) -> llvm::FunctionPointer<'c> {
        let double_ty = ctxt.llvm_context.f64_type();
        let arg_len = self.args.len();
        let arg_tys: Vec<_> = (0..arg_len).map(|_| double_ty).collect();
        let sig = llvm::FunctionType::new(double_ty, &arg_tys[..]);

        let f = ctxt.module.add_function(&self.name.name, sig);
        for i in 0..arg_len {
            f.arg(i).set_name(&self.args[i].name);
        }

        f
    }
}

fn lookup_or_generate_function<'c>(p: &ast::Proto,
                                   ctxt: &Context<'c>)
                                   -> Result<llvm::FunctionPointer<'c>> {
    let arg_len = p.args.len();
    let f: llvm::FunctionPointer<'c> =
        match ctxt.module.get_function(&p.name.name) {
            None => p.skeleton(ctxt),
            Some(f) => f,
        };
    let actual_len = f.num_params();
    if actual_len == arg_len {
        Ok(f)
    } else {
        err(CodegenErrorKind::ArgMismatch { expect: arg_len,
                                            actual: actual_len, })
    }
}

fn codegen_extern<'c>(p: &ast::Proto,
                      ctxt: &Context<'c>) -> Result<Value<'c>> {
    Ok(try!(lookup_or_generate_function(p, ctxt)).to_value())
}

fn codegen_def<'c>(p: &ast::Proto,
                   body: &[Expr],
                   ctxt: &Context<'c>) -> Result<Value<'c>> {
    let f = try!(lookup_or_generate_function(p, ctxt));
    let arg_len = p.args.len();

    if !f.empty() {
        return err(CodegenErrorKind::FunctionRedefinition);
    }

    let bb = f.append(ctxt.llvm_context, "entry");
    ctxt.builder.position_at_end(&bb);
    ctxt.named_values.borrow_mut().clear();
    for i in 0..arg_len {
        let arg = f.arg(i);
        ctxt.named_values
            .borrow_mut()
            .insert(arg.get_name().unwrap().to_owned(), arg.to_value());
    }
    let mut ret_val = None;
    for b in body {
        ret_val = Some(try!(b.codegen(ctxt)));
    }

    match ret_val {
        Some(ret_val) => ctxt.builder.build_ret(ret_val),
        None => return err(CodegenErrorKind::EmptyBody),
    };

    Ok(f.to_value())
}

#[cfg(test)]
use inputs;

#[cfg(test)]
fn with_codegened_inputs<CF, C>(ctxt: Context, each_f: CF, finally: C)
    where CF: Fn(&Context, &inputs::Input, &llvm::FunctionPointer), C: Fn(&Context)
{
    // use llvm::CastFrom; // provides `fn cast`

    // these are definitions so they are included in the dump.
    for i in &inputs::COLLECTED {
        let i = i();
        match i.ast.codegen(&ctxt) {
            Ok(v) => {
                let t = v.get_type();
                // this guard is to work around a presumed bug
                // where `CastFrom for Function` is a little too
                // eager to invoke `ty.get_element()`.
                if !(t.is_function() || t.is_pointer()) {
                    continue;
                }
                if let Some(f) = v.to_function() {
                    each_f(&ctxt, &i, &f);
                }
            }
            Err(e) => {
                panic!("error {:?} when compiling input {}", e, i.str);
            }
        }
    }

    finally(&ctxt);
}

#[test]
fn dump_ir() {
    let llvm_context = llvm::Context::new();
    let ctxt = Context::new(&llvm_context, "kaleido jit");

    with_codegened_inputs(ctxt, |ctxt, i, f| {
        if f.empty() {
            return;
        }
        match f.verify() {
            Ok(()) => {}
            Err(s) => {
                ctxt.module.dump();
                panic!("error {} in verify when compiling input {}", s, i.str);
            }
        }
    }, |ctxt| {
        ctxt.module.dump();
    });
}

#[test]
fn dump_optimized_ir() {
    let llvm_context = llvm::Context::new();
    let ctxt = Context::new(&llvm_context, "kaleido jit");

    let mut fpm = llvm::FunctionPassManager::for_module(&ctxt.module);
    fpm.add_basic_alias_analysis_pass();
    fpm.add_instruction_combining_pass();
    fpm.add_reassociate_pass();
    fpm.add_gvn_pass();
    fpm.add_cfg_simplification_pass();

    fpm.do_initialization();

    with_codegened_inputs(ctxt, |ctxt, i, f| {
        if f.empty() {
            return;
        }
        match f.verify() {
            Ok(()) => {}
            Err(s) => {
                ctxt.module.dump();
                panic!("error {} in verify when compiling input {}", s, i.str);
            }
        }

        fpm.run(*f);

    }, |ctxt| {
        ctxt.module.dump();
    });
}

#[test]
fn demo_fib() {
    use llvm::{ExecutionEngine, VarArgs1Fn}; // provides `JitEngine::new` etc

    let ctx = llvm::Context::new();
    let module = llvm::Module::new("simple", &ctx);
    type N = u64;
    type T = extern "C" fn(N) -> N;
    let f_type = llvm::FunctionType::new(ctx.i64_type(), &[ctx.i64_type()]);
    let func = module.add_function("fib", f_type);
    func.add_attribute(llvm_sys::LLVMNoUnwindAttribute|
                       llvm_sys::LLVMReadNoneAttribute);
    let value = func.arg(0);
    let entry = func.append(&ctx, "entry");
    let on_zero = func.append(&ctx, "on_zero");
    let on_one = func.append(&ctx, "on_one");
    let default = func.append(&ctx, "default");
    let builder = llvm::Builder::new(&ctx);
    let zero = 0u64.compile(&ctx);
    let one = 1u64.compile(&ctx);
    builder.position_at_end(&entry);
    builder.build_switch(*value, &default, &[
        (zero, &on_zero),
        (one, &on_one)
    ]);
    builder.position_at_end(&on_zero);
    builder.build_ret(zero);
    builder.position_at_end(&on_one);
    builder.build_ret(one);
    builder.position_at_end(&default);
    let two = 2u64.compile(&ctx);
    let a = builder.build_isub(*value, one, None);
    let b = builder.build_isub(*value, two, None);
    let fa: llvm::Call = builder.build_call(func, &mut [a], None);
    fa.set_tail_call(true);
    let fb = builder.build_call(func, &mut [b], None);
    fb.set_tail_call(true);
    builder.build_ret(builder.build_iadd(*fa, *fb, None));
    module.verify().unwrap();
    let ee = ExecutionEngine::create_jit_compiler_for_module(module, 0).unwrap();
    ee.with_function(&func, |fib: VarArgs1Fn<u64,u64>| {
        for i in 0..10 {
            println!("fib {} = {}", i, fib.0(i))
        }
    });
}

#[test]
fn demo_three() {
    use llvm::{ExecutionEngine, VarArgs1Fn};

    let ctx = llvm::Context::new();
    let module = llvm::Module::new("simple", &ctx);
    type N = u64;
    type T = extern "C" fn(N, ...) -> N;
    let f_type = llvm::FunctionType::new(ctx.i64_type(), &[ctx.i64_type()]);
    let func = module.add_function("thr", f_type);
    func.add_attribute(llvm_sys::LLVMNoUnwindAttribute|
                       llvm_sys::LLVMReadNoneAttribute);
    let entry = func.append(&ctx, "entry");
    let builder = llvm::Builder::new(&ctx);
    fn n(x: N) -> N { x }
    let three_r = n(3 as N).compile(&ctx);
    builder.position_at_end(&entry);
    builder.build_ret(three_r);
    module.verify().unwrap();
    let ee = ExecutionEngine::create_jit_compiler_for_module(module, 0).unwrap();
    ee.with_function(&func, |fib: VarArgs1Fn<N,N>| {
        for i in 0..10 {
            println!("thr {} = {}", i, fib.0(0 as N))
        }
    });
}

#[test]
fn demo_mcjit() {
    use llvm_sys;
    use llvm::{ExecutionEngine};

    // let llvm_context = llvm::Context::new();
    // let ctxt = ContextState::new(&llvm_context, "kaleido jit");
    // let ctxt = Context::from_context_state(&ctxt);

    // these are definitions so they are included in the dump.
    for i in &inputs::COLLECTED {
        let inputs::Input { ast: i_ast, str: i_str } = i();
        if i_ast.has_free_variables(&[]) {
            continue;
        }
        match i_ast {
            ast::Expr::Extern(..) => continue,
            _ => {}
        }
        let llvm_context = llvm::Context::new();
        let ctxt = Context::new(&llvm_context, "fresh_ctxt");
        type N = f64;
        type T = extern "C" fn(f: f64, ...) -> N;
        match i_ast.codegen(&ctxt) {
            Ok(v) => {
                const ARGS: [f64; 4] = [2.0, 3.0, 4.0, 5.0];
                let (func, arg_count) = match &i_ast {
                    &ast::Expr::Def(ref p, _) => {
                        let arg_count = p.args.len();
                        println!("i: {} [applied to {:?}]", i_str, &ARGS[0..arg_count]);
                        let f = v.to_function().unwrap_or_else(|| {
                            panic!("expected FunctionPointer from Def, got {:?}",
                                   v.get_type())
                        });
                        (f, Some(arg_count))
                    }
                    _ => {
                        println!("i: {}", i_str);
                        let f_type =
                            llvm::FunctionType::new(ctxt.llvm_context.f64_type(),
                                                    &[ctxt.llvm_context.f64_type()]);
                        let func = ctxt.module.add_function("fresh_fun", f_type);
                        func.add_attribute(llvm_sys::LLVMNoUnwindAttribute|
                                           llvm_sys::LLVMReadNoneAttribute);
                        let entry = func.append(ctxt.llvm_context, "entry");
                        let builder = llvm::Builder::new(ctxt.llvm_context);
                        let builder = ctxt.builder;
                        builder.position_at_end(&entry);
                        builder.build_ret(v);
                        (func, None)
                    }
                };

                ctxt.module.verify().unwrap();
                let jit = ExecutionEngine::create_jit_compiler_for_module(ctxt.module, 0).unwrap();
                let first_r: f64 = match arg_count {
                    None => jit.get_function::<(f64,), f64>(&func)(4.0),
                    Some(0) => jit.get_function::<(), f64>(&func)(),
                    Some(1) => jit.get_function::<(f64,), f64>(&func)(ARGS[0]),
                    Some(2) => jit.get_function::<(f64,f64), f64>(&func)(ARGS[0], ARGS[1]),
                    Some(3) => jit.get_function::<(f64,f64,f64), f64>(&func)(ARGS[0], ARGS[1], ARGS[2]),
                    Some(4) => jit.get_function::<(f64,f64,f64,f64), f64>(&func)(ARGS[0], ARGS[1], ARGS[2], ARGS[3]),
                    Some(c) => panic!("unhandled arg count {}", c),
                };

                println!("result: {}", first_r);
            }
            Err(e) => {
                panic!("error {:?} when compiling input {}", e, i_str);
            }
        }
    }
}
```
