```rust
use llvm_sys::execution_engine::*;
use llvm_sys::prelude::*;
use llvm_sys::target;

use super::*;
use super::c_name;

use libc::{c_char, c_uint, c_void};

use std::ffi::{CStr};
use std::marker::PhantomData;
use std::mem;

impl<'c> Drop for ExecutionEngine<'c> {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeExecutionEngine(self.llvm_execution_engine_ref);
        }
    }
}

pub struct ExecutionEngine<'c> {
    llvm_execution_engine_ref: LLVMExecutionEngineRef,
    a: PhantomData<&'c ()>,
}

pub struct VarArgs1Fn<A,R>(pub extern "C" fn(A, ...) -> R);
pub struct VarArgs2Fn<A,B,R>(pub extern "C" fn(A, B, ...) -> R);
pub struct VarArgs3Fn<A,B,C,R>(pub extern "C" fn(A, B, C, ...) -> R);
pub struct VarArgs4Fn<A,B,C,D,R>(pub extern "C" fn(A, B, C, D, ...) -> R);

pub struct Args0Fn<R>(pub extern "C" fn() -> R);
pub struct Args1Fn<A,R>(pub extern "C" fn(A) -> R);
pub struct Args2Fn<A,B,R>(pub extern "C" fn(A, B) -> R);
pub struct Args3Fn<A,B,C,R>(pub extern "C" fn(A, B, C) -> R);
pub struct Args4Fn<A,B,C,D,R>(pub extern "C" fn(A, B, C, D) -> R);

pub enum Void { }

trait FnArgs: Sized {
    type A;
    type B;
    type C;
    type D;
    fn to_t0(self) -> () { panic!("unsupported") }
    fn to_t1(self) -> (Self::A,) { panic!("unsupported") }
    fn to_t2(self) -> (Self::A,Self::B) { panic!("unsupported") }
    fn to_t3(self) -> (Self::A,Self::B,Self::C) { panic!("unsupported") }
    fn to_t4(self) -> (Self::A,Self::B,Self::C,Self::D) { panic!("unsupported") }
}

impl FnArgs for () {
    type A = Void; type B = Void; type C = Void; type D = Void;
    fn to_t0(self) -> () { () }
}
impl<A> FnArgs for (A,) {
    type A = A; type B = Void; type C = Void; type D = Void;
    fn to_t1(self) -> (Self::A,) { self }
}
impl<A,B> FnArgs for (A,B) {
    type A = A; type B = B; type C = Void; type D = Void;
    fn to_t2(self) -> (Self::A,Self::B) { self }
}
impl<A,B,C> FnArgs for (A,B,C) {
    type A = A; type B = B; type C = C; type D = Void;
    fn to_t3(self) -> (Self::A,Self::B,Self::C) { self }
}
impl<A,B,C,D> FnArgs for (A,B,C,D) {
    type A = A; type B = B; type C = C; type D = D;
    fn to_t4(self) -> (Self::A,Self::B,Self::C,Self::D) { self }
}

macro_rules! fn_impls {
    (() $ArgsNFn:ident, let $t:ident = $to_t:ident; ($($t_:expr),*)) => {
        impl<R,Args:FnArgs> FnOnce<Args> for $ArgsNFn<R> {
            type Output = R;
            extern "rust-call" fn call_once(self, args: Args) -> R {
                let $t = args.$to_t(); (self.0)($($t_),*) } }
        impl<R,Args:FnArgs> FnMut<Args> for $ArgsNFn<R> {
            extern "rust-call" fn call_mut(&mut self, args: Args) -> R {
                let $t = args.$to_t(); (self.0)($($t_),*) } }
        impl<R,Args:FnArgs> Fn<Args> for $ArgsNFn<R> {
            extern "rust-call" fn call(&self, args: Args) -> R {
                let $t = args.$to_t(); (self.0)($($t_),*) } }
    };
    (($($A:ident),*) $ArgsNFn:ident, let $t:ident = $to_t:ident; ($($t_:expr),*)) => {
        impl<R,Args:FnArgs> FnOnce<Args> for $ArgsNFn<$(Args::$A),*,R> {
            type Output = R;
            extern "rust-call" fn call_once(self, args: Args) -> R {
                let $t = args.$to_t(); (self.0)($($t_),*) } }
        impl<R,Args:FnArgs> FnMut<Args> for $ArgsNFn<$(Args::$A),*,R> {
            extern "rust-call" fn call_mut(&mut self, args: Args) -> R {
                let $t = args.$to_t(); (self.0)($($t_),*) } }
        impl<R,Args:FnArgs> Fn<Args> for $ArgsNFn<$(Args::$A),*,R> {
            extern "rust-call" fn call(&self, args: Args) -> R {
                let $t = args.$to_t(); (self.0)($($t_),*) } }
    }
}

fn_impls!(()        Args0Fn, let _t = to_t0; ());
fn_impls!((A)       Args1Fn, let  t = to_t1; (t.0));
fn_impls!((A,B)     Args2Fn, let  t = to_t2; (t.0, t.1));
fn_impls!((A,B,C)   Args3Fn, let  t = to_t3; (t.0, t.1, t.2));
fn_impls!((A,B,C,D) Args4Fn, let  t = to_t4; (t.0, t.1, t.2, t.3));

fn_impls!((A)       VarArgs1Fn, let  t = to_t1; (t.0));
fn_impls!((A,B)     VarArgs2Fn, let  t = to_t2; (t.0, t.1));
fn_impls!((A,B,C)   VarArgs3Fn, let  t = to_t3; (t.0, t.1, t.2));
fn_impls!((A,B,C,D) VarArgs4Fn, let  t = to_t4; (t.0, t.1, t.2, t.3));

// fn_impls!(<> (A,B,C);   Args3Fn, let t =  to_t3; (t.0, t.1, t.2));
// fn_impls!(<> (A,B,C,D); Args4Fn, let t =  to_t4; (t.0, t.1, t.2, t.3));
// 
// fn_impls!(<> (A);       VarArgs1Fn, let t =  to_t1; (t.0));
// fn_impls!(<> (A,B);     VarArgs2Fn, let t =  to_t2; (t.0, t.1));
// fn_impls!(<> (A,B,C);   VarArgs3Fn, let t =  to_t3; (t.0, t.1, t.2));
// fn_impls!(<> (A,B,C,D); VarArgs4Fn, let t =  to_t4; (t.0, t.1, t.2, t.3));

impl<'c> ExecutionEngine<'c> {
    fn build_it<R>(m: Module<'c>, handle: R) -> Result<ExecutionEngine<'c>, String>
        where R: Fn(&mut LLVMExecutionEngineRef,
                    LLVMModuleRef,
                    &mut *mut c_char) // SIC
                    -> LLVMBool
    {
        let mut ee: LLVMExecutionEngineRef;
        let mut error_msg: *mut c_char;
        unsafe {
            if 0 != target::LLVM_InitializeNativeAsmPrinter() {
                return Err("LLVM_InitializeNativeAsmPrinter failure".to_string());
            }
            if 0 != target::LLVM_InitializeNativeAsmParser() {
                return Err("LLVM_InitializeNativeAsmParser failure".to_string());
            }
            if 0 != target::LLVM_InitializeNativeTarget() {
                return Err("LLVM_InitializeNativeTarget failure".to_string());
            }
            ee = mem::uninitialized();
            error_msg = mem::uninitialized();

            // AFAICT from the LLVM source code, all of the execution engine
            // constructors are taking ownership of the LLVMModuleRef that
            // they are passed. (Ah good old C signatures...)
            //
            // We emulate the effect of this by forgetting our own module,
            // so that we do not run its destructor twice.
            let mref = m.llvm_module_ref;
            mem::forget(m);
            if 0 == handle(&mut ee, mref, &mut error_msg) {
                // ==> ee
                Ok(ExecutionEngine {
                    a: PhantomData, llvm_execution_engine_ref: ee,
                })
            } else {
                // ==> error
                let name = CStr::from_ptr(error_msg);
                Err(name.to_str().unwrap().to_owned())
            }
        }
    }

    pub fn new_for_module(m: Module<'c>) -> Result<ExecutionEngine<'c>, String> {
        ExecutionEngine::build_it(m, |ee_ref, m_ref, error_msg_ref| {
            unsafe {
                LLVMLinkInMCJIT();
                LLVMCreateExecutionEngineForModule(ee_ref,
                                                   m_ref,
                                                   error_msg_ref) }
        })
    }

    pub fn interpreter_for_module(m: Module<'c>) -> Result<ExecutionEngine<'c>, String> {
        ExecutionEngine::build_it(m, |ee_ref, m_ref, error_msg_ref| {
            unsafe {
                LLVMLinkInInterpreter();
                LLVMCreateInterpreterForModule(ee_ref,
                                               m_ref,
                                               error_msg_ref) }
        })
    }

    pub fn create_jit_compiler_for_module(m: Module<'c>,
                                          opt_level: u32) -> Result<ExecutionEngine<'c>, String> {
        ExecutionEngine::build_it(m, |ee_ref, m_ref, error_msg_ref| {
            unsafe {
                LLVMLinkInMCJIT();
                LLVMCreateJITCompilerForModule(ee_ref,
                                               m_ref,
                                               opt_level as c_uint,
                                               error_msg_ref) }
        })
    }

    fn pointer_to_global(&self, global: Value<'c>) -> *mut c_void {
        unsafe {
            LLVMGetPointerToGlobal(self.llvm_execution_engine_ref,
                                   global.llvm_value_ref)
        }
    }

    fn address_of_named_global(&self, name: &str) -> usize {
        let name = c_name(Some(name));
        unsafe {
            LLVMGetGlobalValueAddress(self.llvm_execution_engine_ref,
                                      name.as_ptr()) as usize
        }
    }

    fn address_of_named_function(&self, name: &str) -> usize {
        let name = c_name(Some(name));
        unsafe {
            LLVMGetFunctionAddress(self.llvm_execution_engine_ref,
                                   name.as_ptr()) as usize
        }
    }

    unsafe fn get_va1_function<A, R>(&self, f: &FunctionPointer<'c>) -> VarArgs1Fn<A,R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_va2_function<A, B, R>(&self, f: &FunctionPointer<'c>) -> VarArgs2Fn<A,B,R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_va3_function<A, B, C, R>(&self, f: &FunctionPointer<'c>) -> VarArgs3Fn<A,B,C,R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_va4_function<A, B, C, D, R>(&self, f: &FunctionPointer<'c>) -> VarArgs4Fn<A,B,C,D,R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_0_function<R>(&self, f: &FunctionPointer<'c>) -> Args0Fn<R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_1_function<A,R>(&self, f: &FunctionPointer<'c>) -> Args1Fn<A,R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_2_function<A,B,R>(&self, f: &FunctionPointer<'c>) -> Args2Fn<A,B,R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_3_function<A,B,C,R>(&self, f: &FunctionPointer<'c>) -> Args3Fn<A,B,C,R>
    { mem::transmute(self.pointer_to_global(f.v)) }

    unsafe fn get_4_function<A,B,C,D,R>(&self, f: &FunctionPointer<'c>) -> Args4Fn<A,B,C,D,R>
    { mem::transmute(self.pointer_to_global(f.v)) }


    // Arguably the 'c bound on Args and Ret is nonsense -- why should the data
    // processed by the function have anything to do with the lifetime bound of
    // the function itself?
    pub fn get_function<Args:'c, Ret:'c>(&self, f: &FunctionPointer<'c>) -> Box<Fn<Args, Output=Ret>+'c>
        where Args: FnArgs
    {
        let ft = f.get_function_type();
        unsafe {
            match (ft.count_param_types(), ft.is_var_arg()) {
                (0, false) => Box::new(self.get_0_function(f)),
                (1, false) => Box::new(self.get_1_function(f)),
                (2, false) => Box::new(self.get_2_function(f)),
                (3, false) => Box::new(self.get_3_function(f)),
                (4, false) => Box::new(self.get_4_function(f)),

                (1, true) => Box::new(self.get_va1_function(f)),
                (2, true) => Box::new(self.get_va2_function(f)),
                (3, true) => Box::new(self.get_va3_function(f)),
                (4, true) => Box::new(self.get_va4_function(f)),

                _ => panic!("unimplemented function type"),
            }
        }
    }

    pub fn with_function<A, B, C, D>(&self,
                                     f: &FunctionPointer<'c>,
                                     cb: C) -> D
        where A:Compile, B:Compile, C: FnOnce(VarArgs1Fn<A,B>) -> D
    {
        unsafe {
            cb(self.get_va1_function::<A, B>(f))
        }
    }
}
```
