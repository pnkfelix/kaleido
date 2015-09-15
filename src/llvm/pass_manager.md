```rust
use llvm_sys::prelude::*;
use llvm_sys::core::*;
use llvm_sys::transforms::scalar::*;

use super::*;

use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

impl<'m> Drop for PassManager<'m> {
    fn drop(&mut self) {
        unsafe { LLVMDisposePassManager(self.llvm_pass_manager_ref); }
    }
}

impl<'m> PassManager<'m> {
    pub fn new() -> PassManager<'m> {
        unsafe {
            PassManager { a: PhantomData,
                          llvm_pass_manager_ref: LLVMCreatePassManager() }
        }
    }
}

pub struct PassManager<'m> {
    a: PhantomData<&'m ()>,
    llvm_pass_manager_ref: LLVMPassManagerRef
}

pub struct FunctionPassManager<'m> {
    p: PassManager<'m>,
}

impl<'m> Deref for FunctionPassManager<'m> {
    type Target = PassManager<'m>;
    fn deref(&self) -> &Self::Target { &self.p }
}

impl<'m> DerefMut for FunctionPassManager<'m> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.p }
}

impl<'m> FunctionPassManager<'m> {
    pub fn for_module(m: &Module<'m>) -> FunctionPassManager<'m> {
        let lref = unsafe {
            LLVMCreateFunctionPassManagerForModule(m.llvm_module_ref)
        };
        FunctionPassManager{
            p: PassManager { a: PhantomData,
                             llvm_pass_manager_ref: lref  }
        }
    }
}

impl<'m> PassManager<'m> {
    pub fn add_basic_alias_analysis_pass(&mut self) {
        unsafe { LLVMAddBasicAliasAnalysisPass(self.llvm_pass_manager_ref) }
    }
    pub fn add_instruction_combining_pass(&mut self) {
        unsafe { LLVMAddInstructionCombiningPass(self.llvm_pass_manager_ref) }
    }
    pub fn add_reassociate_pass(&mut self) {
        unsafe { LLVMAddReassociatePass(self.llvm_pass_manager_ref) }
    }
    pub fn add_gvn_pass(&mut self) {
        unsafe { LLVMAddGVNPass(self.llvm_pass_manager_ref) }
    }
    pub fn add_cfg_simplification_pass(&mut self) {
        unsafe { LLVMAddCFGSimplificationPass(self.llvm_pass_manager_ref) }
    }
}

impl<'m> FunctionPassManager<'m> {
    /// Initializes all of the function passes scheduled in the
    /// function pass manager. Returns true if any of the passes
    /// modified the module, false otherwise.
    ///
    /// (Felix asks: "the module"?  What module? Thre's no other input.)
    pub fn do_initialization(&self) -> bool {
        unsafe { LLVMInitializeFunctionPassManager(self.llvm_pass_manager_ref) != 0 }
    }

    pub fn run<'c>(&self, f: FunctionPointer<'c>) -> RunResult {
        let r = unsafe { LLVMRunFunctionPassManager(self.llvm_pass_manager_ref,
                                                    f.llvm_value_ref) };
        match r {
            1 => RunResult::InputModified,
            _ => RunResult::InputUnmodified,
        }
    }
}

pub enum RunResult {
    InputModified,
    InputUnmodified,
}
```
