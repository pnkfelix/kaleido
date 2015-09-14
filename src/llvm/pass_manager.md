```rust
use llvm_sys::prelude::*;
use llvm_sys::core::*;
use llvm_sys::transforms::scalar::*;

use super::*;

impl Drop for PassManager {
    fn drop(&mut self) {
        unsafe { LLVMDisposePassManager(self.llvm_pass_manager_ref); }
    }
}

pub struct PassManager {
    llvm_pass_manager_ref: LLVMPassManagerRef
}

impl PassManager {
    pub fn new() -> PassManager {
        unsafe {
            PassManager { llvm_pass_manager_ref: LLVMCreatePassManager() }
        }
    }

    pub fn fpm_for_module(m: &Module) -> PassManager {
        unsafe {
            PassManager {
                llvm_pass_manager_ref:
                LLVMCreateFunctionPassManagerForModule(m.llvm_module_ref)
            }
        }
    }

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

    /// Initializes all of the function passes scheduled in the
    /// function pass manager. Returns true if any of the passes
    /// modified the module, false otherwise.
    ///
    /// (Felix asks: "the module"?  What module? Thre's no other input.)
    pub fn do_initialization(&self) -> bool {
        unsafe { LLVMInitializeFunctionPassManager(self.llvm_pass_manager_ref) != 0 }
    }

    pub fn run<'c>(&self, f: FunctionPointer<'c>) { unimplemented!() }
}
```
