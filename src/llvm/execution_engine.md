```rust
use llvm_sys::execution_engine::*;
use llvm_sys::prelude::*;

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

impl<'c> ExecutionEngine<'c> {
    fn build_it<R>(m: &Module<'c>, handle: R) -> Result<ExecutionEngine<'c>, String>
        where R: Fn(&mut LLVMExecutionEngineRef,
                    LLVMModuleRef,
                    &mut *mut c_char) // SIC
                    -> LLVMBool
    {
        let mut ee: LLVMExecutionEngineRef;
        let mut error_msg: *mut c_char;
        unsafe {
            ee = mem::uninitialized();
            error_msg = mem::uninitialized();
            if 0 == handle(&mut ee, m.llvm_module_ref, &mut error_msg) {
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

    pub fn new_for_module(m: &Module<'c>) -> Result<ExecutionEngine<'c>, String> {
        ExecutionEngine::build_it(m, |ee_ref, m_ref, error_msg_ref| {
            unsafe { LLVMCreateExecutionEngineForModule(ee_ref,
                                                        m_ref,
                                                        error_msg_ref) }
        })
    }

    pub fn interpreter_for_module(m: &Module<'c>) -> Result<ExecutionEngine<'c>, String> {
        ExecutionEngine::build_it(m, |ee_ref, m_ref, error_msg_ref| {
            unsafe { LLVMCreateInterpreterForModule(ee_ref,
                                                    m_ref,
                                                    error_msg_ref) }
        })
    }

    pub fn create_jit_compiler_for_module(m: &Module<'c>,
                                      opt_level: u32) -> Result<ExecutionEngine<'c>, String> {
        ExecutionEngine::build_it(m, |ee_ref, m_ref, error_msg_ref| {
            unsafe { LLVMCreateJITCompilerForModule(ee_ref,
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

    unsafe fn get_function<A, B>(&self,
                                 f: &FunctionPointer<'c>) -> (extern fn(A) -> B) {
        mem::transmute(self.pointer_to_global(f.v))
    }

    pub fn with_function<A, B, C, D>(&self,
                                     context: &Context<'c>,
                                     f: &FunctionPointer<'c>,
                                     cb: C) -> D
        where A:Compile, B:Compile, C: FnOnce(extern fn(A) -> B) -> D {
            unsafe {
                cb(self.get_function::<A, B>(f))
            }
    }
}
```
