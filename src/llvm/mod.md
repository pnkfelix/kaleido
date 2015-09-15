```rust
#![allow(dead_code, unused_variables)]

use self::fun_ctors::*;

use llvm_sys::prelude::*;
use llvm_sys::core::*;
use llvm_sys::{self, LLVMAttribute, LLVMTypeKind};
use llvm_ext::sys::LLVMVerifyFunctionWithOutput;

use libc::{c_char, c_uint};

use std::ffi::{CStr, CString};
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;

pub use self::pass_manager::{PassManager, FunctionPassManager};
pub use self::execution_engine::ExecutionEngine;
pub use self::execution_engine::{Args0Fn};
pub use self::execution_engine::{Args1Fn, VarArgs1Fn};
pub use self::execution_engine::{Args2Fn, VarArgs2Fn};
pub use self::execution_engine::{Args3Fn, VarArgs3Fn};
pub use self::execution_engine::{Args4Fn, VarArgs4Fn};

mod pass_manager;
mod execution_engine;

pub struct Context<'c> {
    a: PhantomData<&'c ()>,
    llvm_context_ref: LLVMContextRef,
}

#[derive(Copy, Clone)]
pub struct Value<'c> {
    a: PhantomData<&'c ()>,
    llvm_value_ref: LLVMValueRef,
}

pub trait ToValue<'c> {
    fn to_value(&self) -> Value<'c>;
}

macro_rules! wrapper_value {
    ($SubValue:ident) => {
        impl<'c> Deref for $SubValue<'c> {
            type Target = Value<'c>;
            fn deref(&self) -> &Self::Target { &self.v }
        }

        impl<'c> ToValue<'c> for $SubValue<'c> {
            fn to_value(&self) -> Value<'c> {
                Value { a: self.a, llvm_value_ref: self.llvm_value_ref }
            }
        }

        #[derive(Copy, Clone)]
        pub struct $SubValue<'c> {
            v: Value<'c>,
        }
    }
}


wrapper_value!(FunctionPointer);
wrapper_value!(Arg);
wrapper_value!(Call);

pub struct Module<'m> {
    a: PhantomData<&'m ()>,
    llvm_module_ref: LLVMModuleRef,
}

impl<'m> Drop for Module<'m> {
    fn drop(&mut self) {
        unsafe { LLVMDisposeModule(self.llvm_module_ref); }
    }
}

#[derive(Copy, Clone)]
pub struct Type<'c> {
    llvm_type_ref: LLVMTypeRef,
    a: PhantomData<&'c ()>,
}

impl Drop for Message {
    fn drop(&mut self) { unsafe { LLVMDisposeMessage(self.0) } }
}
impl fmt::Debug for Message {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        write!(w, "Message({})", self.c_str().to_string_lossy())
    }
}
impl fmt::Display for Message {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        write!(w, "{}", self.c_str().to_string_lossy())
    }
}
struct Message(*mut c_char);
impl Message {
    fn c_str(&self) -> &CStr {
        unsafe {
            CStr::from_ptr(self.0)
        }
    }
}

pub trait Printed { fn printed(&self) -> Message; }

impl<'c> Printed for Type<'c> {
    fn printed(&self) -> Message {
        unsafe { Message(LLVMPrintTypeToString(self.llvm_type_ref)) }
    }
}

impl<'c> Printed for Module<'c> {
    fn printed(&self) -> Message {
        unsafe { Message(LLVMPrintModuleToString(self.llvm_module_ref)) }
    }
}

impl<'c> Printed for Value<'c> {
    fn printed(&self) -> Message {
        unsafe{ Message(LLVMPrintValueToString(self.llvm_value_ref)) }
    }
}

macro_rules! wrapper_subtype {
    ($SomeType:ident, $SuperType:ident) => {
        impl<'c> Deref for $SomeType<'c> {
            type Target = $SuperType<'c>;
            fn deref(&self) -> &Self::Target { &self.t }
        }

        pub struct $SomeType<'c> {
            t: $SuperType<'c>,
        }
    }
}

wrapper_subtype!(PointerType, Type);
wrapper_subtype!(FunctionType, Type);

macro_rules! debug_printed {
    ($SomeType:ident) => {
        impl<'c> fmt::Debug for $SomeType<'c> {
            fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
                let m = self.printed();
                write!(w, "{}(`{}`)", stringify!($SomeType), m.c_str().to_string_lossy())
            }
        }
    }
}

debug_printed!(Type);
debug_printed!(FunctionType);
debug_printed!(PointerType);

impl<'c> PointerType<'c> {
    fn element_type(&self) -> Type<'c> {
        let t = unsafe { LLVMGetElementType(self.t.llvm_type_ref) };
        Type(t)
    }
}

impl<'c> FunctionType<'c> {
    fn new_core(ret: Type<'c>, args: &[Type<'c>], is_var_arg: bool) -> FunctionType<'c> {
        let r = unsafe {
            FunctionType(LLVMFunctionType(ret.llvm_type_ref,
                                          mem::transmute(args.as_ptr()),
                                          args.len() as c_uint,
                                          if is_var_arg { 1 } else { 0 }))
        };
        // println!("FunctionType::new(ret: {:?}, args: {:?}) => {:?}", ret, args, r);
        assert_eq!(r.count_param_types(), args.len());
        r
    }

    pub fn new(ret: Type<'c>, args: &[Type<'c>]) -> FunctionType<'c> {
        FunctionType::new_core(ret, args, false)
    }

    pub fn new_var_arg(ret: Type<'c>, args: &[Type<'c>]) -> FunctionType<'c> {
        FunctionType::new_core(ret, args, true)
    }

    pub fn is_var_arg(&self) -> bool {
        unsafe {
            LLVMIsFunctionVarArg(self.t.llvm_type_ref) == 1
        }
    }

    pub fn return_type(&self) -> Type<'c> {
        unsafe {
            Type(LLVMGetReturnType(self.t.llvm_type_ref))
        }
    }

    fn count_param_types(&self) -> usize {
        unsafe { LLVMCountParamTypes(self.t.llvm_type_ref) as usize }
    }

    pub fn param_types(&self) -> Vec<Type<'c>> {
        let count = self.count_param_types();
        let mut v: Vec<Type<'c>> = Vec::with_capacity(count);
        let p = v.as_mut_ptr();
        unsafe {
            LLVMGetParamTypes(self.t.llvm_type_ref, p as *mut LLVMTypeRef);
            mem::forget(v);
            Vec::from_raw_parts(p, count, count)
        }
    }
}

pub enum Predicate {
    LessThan,
}

pub trait Compile {
    fn compile<'c>(&self, c: &Context<'c>) -> Value<'c>;
}

impl<'c> Drop for Context<'c> {
    fn drop(&mut self) { unsafe { LLVMContextDispose(self.llvm_context_ref) } }
}
impl<'c> Context<'c> {
    pub fn new() -> Context<'c> {
        let lref = unsafe { LLVMContextCreate() };
        Context { a: PhantomData, llvm_context_ref: lref }
    }
    pub fn get_type<T:Compile>(&self) -> &'c Type {
        unimplemented!()
    }
    pub fn f64_type(&self) -> Type<'c> {
        unsafe { Type(LLVMDoubleTypeInContext(self.llvm_context_ref)) }
    }
    pub fn f32_type(&self) -> Type<'c> {
        unsafe { Type(LLVMFloatTypeInContext(self.llvm_context_ref)) }
    }

    pub fn i64_type(&self) -> Type<'c> {
        unsafe { Type(LLVMInt64TypeInContext(self.llvm_context_ref)) }
    }
    pub fn i32_type(&self) -> Type<'c> {
        unsafe { Type(LLVMInt32TypeInContext(self.llvm_context_ref)) }
    }
    pub fn i16_type(&self) -> Type<'c> {
        unsafe { Type(LLVMInt16TypeInContext(self.llvm_context_ref)) }
    }
    pub fn i8_type(&self) -> Type<'c> {
        unsafe { Type(LLVMInt8TypeInContext(self.llvm_context_ref)) }
    }
    pub fn i1_type(&self) -> Type<'c> {
        unsafe { Type(LLVMInt1TypeInContext(self.llvm_context_ref)) }
    }
    #[allow(non_snake_case)]
    pub fn iN_type(&self, num_bits: u32) -> Type<'c> {
        unsafe { Type(LLVMIntTypeInContext(self.llvm_context_ref, num_bits)) }
    }
}

impl Compile for u64 {
    fn compile<'c>(&self, context: &Context<'c>) -> Value<'c> {
        let sign_extend = 0;
        let t = context.i64_type();
        let r = unsafe { LLVMConstInt(t.llvm_type_ref, *self, sign_extend) };
        Value { a: PhantomData, llvm_value_ref: r }
    }
}

impl Compile for f64 {
    fn compile<'c>(&self, context: &Context<'c>) -> Value<'c> {
        let r = unsafe {
            LLVMConstReal(LLVMDoubleTypeInContext(context.llvm_context_ref), *self)
        };
        Value { a: PhantomData, llvm_value_ref: r }
    }
}
impl Compile for f32 {
    fn compile<'c>(&self, context: &Context<'c>) -> Value<'c> {
        let r = unsafe {
            LLVMConstReal(LLVMFloatTypeInContext(context.llvm_context_ref), *self as f64)
        };
        Value { a: PhantomData, llvm_value_ref: r }
    }
}

impl<'c> Value<'c> {
    pub fn get_type(&self) -> Type {
        let r = unsafe { LLVMTypeOf(self.llvm_value_ref) };
        Type(r)
    }
    pub fn to_function(&self) -> Option<FunctionPointer> {
        // println!("Value::to_function k: {:?}", kind_str(self.get_type().kind()));
        let mut t = self.get_type();
        while let Some(p) = t.to_pointer() {
            t = p.element_type();
        }
        if t.is_function() {
            Some(Function(self.llvm_value_ref))
        } else {
            None
        }
    }
    pub fn set_name(&self, name: &str) {
        let name = CString::new(name).unwrap();
        unsafe {
            LLVMSetValueName(self.llvm_value_ref, name.as_ptr());
        }
    }
    pub fn get_name(&self) -> Option<String> {
        unsafe {
            let ptr = LLVMGetValueName(self.llvm_value_ref);
            if ptr.is_null() {
                None
            } else {
                let name = CStr::from_ptr(ptr);
                Some(name.to_str().unwrap().to_owned())
            }
        }
    }
}

fn kind_str(k: LLVMTypeKind) -> &'static str {
    match k {
        LLVMTypeKind::LLVMVoidTypeKind => "VoidTypeKind",
        LLVMTypeKind::LLVMHalfTypeKind => "HalfTypeKind",
        LLVMTypeKind::LLVMFloatTypeKind => "FloatTypeKind",
        LLVMTypeKind::LLVMDoubleTypeKind => "DoubleTypeKind",
        LLVMTypeKind::LLVMX86_FP80TypeKind => "X86_FP80TypeKind",
        LLVMTypeKind::LLVMFP128TypeKind => "FP128TypeKind",
        LLVMTypeKind::LLVMPPC_FP128TypeKind => "PPC_FP128TypeKind",
        LLVMTypeKind::LLVMLabelTypeKind => "LabelTypeKind",
        LLVMTypeKind::LLVMIntegerTypeKind => "IntegerTypeKind",
        LLVMTypeKind::LLVMFunctionTypeKind => "FunctionTypeKind",
        LLVMTypeKind::LLVMStructTypeKind  => "StructTypeKind",
        LLVMTypeKind::LLVMArrayTypeKind => "ArrayTypeKind",
        LLVMTypeKind::LLVMPointerTypeKind => "PointerTypeKind",
        LLVMTypeKind::LLVMVectorTypeKind => "VectorTypeKind",
        LLVMTypeKind::LLVMMetadataTypeKind => "MetadataTypeKind",
        LLVMTypeKind::LLVMX86_MMXTypeKind => "X86_MMXTypeKind",
    }
}

impl<'c> Type<'c> {
    pub fn kind(&self) -> LLVMTypeKind {
        unsafe { LLVMGetTypeKind(self.llvm_type_ref) }
    }
    pub fn is_function(&self) -> bool {
        self.kind() as usize == LLVMTypeKind::LLVMFunctionTypeKind as usize
    }
    pub fn is_pointer(&self) -> bool {
        self.kind() as usize == LLVMTypeKind::LLVMPointerTypeKind as usize
    }
    pub fn to_function(self) -> Option<FunctionType<'c>> {
        if self.is_function() {
            Some(FunctionType(self.llvm_type_ref))
        } else {
            None
        }
    }
    pub fn to_pointer(self) -> Option<PointerType<'c>> {
        if self.is_pointer() {
            Some(PointerType(self.llvm_type_ref))
        } else {
            None
        }
    }
}

pub struct Block<'c> {
    a: PhantomData<&'c ()>,
    llvm_basic_block_ref: LLVMBasicBlockRef,
}

impl<'c> FunctionPointer<'c> {
    pub fn num_params(&self) -> usize {
        let t = self.get_function_type();
        // println!("FunctionPointer::num_params t: {:?}", t);
        let c = t.count_param_types();
        // println!("FunctionPointer param_type count: {}", c);
        c
    }
    pub fn get_type(&self) -> PointerType {
        let t = self.v.get_type();
        assert!(t.is_pointer());
        PointerType(t.llvm_type_ref)
    }
    pub fn get_function_type(&self) -> FunctionType {
        let mut t = self.v.get_type();
        while let Some(p) = t.to_pointer() {
            t = p.element_type();
        }
        assert!(t.is_function());
        FunctionType(t.llvm_type_ref)
    }
    pub fn arg(&self, i: usize) -> Arg<'c> {
        let v = unsafe { LLVMGetParam(self.v.llvm_value_ref, i as c_uint) };
        Arg { v: Value(v) }
    }
    pub fn add_attribute(&self, a: LLVMAttribute) {
        unsafe { LLVMAddFunctionAttr(self.v.llvm_value_ref, a) }
    }
    pub fn get_signature(&self) -> FunctionType {
        self.get_function_type()
    }
    pub fn count_basic_blocks(&self) -> usize {
        unsafe { LLVMCountBasicBlocks(self.v.llvm_value_ref) as usize }
    }
    pub fn empty(&self) -> bool {
        self.count_basic_blocks() == 0
    }

    pub fn append(&self, ctxt: &Context<'c>, name: &str) -> Block<'c> {
        let name = CString::new(name).unwrap();
        let b = unsafe { LLVMAppendBasicBlockInContext(ctxt.llvm_context_ref,
                                                       self.v.llvm_value_ref,
                                                       name.as_ptr()) };
        Block(b)
    }

    pub fn verify(&self) -> Result<(), Message> {
        unsafe {
            let mut msg: *mut c_char = mem::uninitialized();
            let ret =
                LLVMVerifyFunctionWithOutput(self.v.llvm_value_ref,
                                             llvm_sys::analysis::LLVMVerifierFailureAction::LLVMReturnStatusAction,
                                             // llvm_sys::analysis::LLVMVerifierFailureAction::LLVMPrintMessageAction,
                                             // llvm_sys::analysis::LLVMVerifierFailureAction::LLVMAbortProcessAction,
                                             &mut msg);
            if ret == 1 {
                Err(Message(msg))
            } else {
                Ok(())
            }
        }
    }
}

impl<'c> Arg<'c> {
    pub fn add_attributes(&self, a: LLVMAttribute) {
        unsafe { LLVMAddAttribute(self.v.llvm_value_ref, a) }
    }
    pub fn remove_attributes(&self, a: LLVMAttribute) {
        unsafe { LLVMRemoveAttribute(self.v.llvm_value_ref, a) }
    }
    pub fn get_attributes(&self) -> LLVMAttribute {
        unsafe { LLVMGetAttribute(self.v.llvm_value_ref) }
    }
}

impl<'c> Call<'c> {
    pub fn set_tail_call(&self, flag: bool) {
        unsafe { LLVMSetTailCall(self.v.llvm_value_ref, if flag { 1 } else { 0 }) }
    }
    pub fn is_tail_call(&self) -> bool {
        unsafe { LLVMIsTailCall(self.v.llvm_value_ref) != 0 }
    }
}

impl<'c> Drop for Builder<'c> {
    fn drop(&mut self) {
        unsafe { LLVMDisposeBuilder(self.llvm_builder_ref); }
    }
}

pub struct Builder<'c> {
    a: PhantomData<&'c ()>,
    llvm_builder_ref: LLVMBuilderRef,
}

struct CName(CString);
fn c_name(name: Option<&str>) -> CName {
    let name = name.unwrap_or("");
    CName(CString::new(name).unwrap())
}
impl CName {
    fn as_ptr(&self) -> *const c_char {
        self.0.as_bytes_with_nul().as_ptr() as *const c_char
    }
}


impl<'c> Builder<'c> {
    pub fn new(llvm_context: &Context<'c>) -> Builder<'c> {
        let bref = unsafe {
            LLVMCreateBuilderInContext(llvm_context.llvm_context_ref)
        };
        Builder { a: PhantomData, llvm_builder_ref: bref }
    }
    pub fn position_at_end(&self, block: &Block) {
        unsafe {
            LLVMPositionBuilderAtEnd(self.llvm_builder_ref, block.llvm_basic_block_ref)
        }
    }
    pub fn build_call(&self, a: FunctionPointer<'c>, mut args: &mut [Value<'c>],
                      name: Option<&str>) -> Call<'c> {
        let name = c_name(name);
        let name = name.as_ptr() as *const c_char;
        unsafe {
            Call { v: Value(LLVMBuildCall(self.llvm_builder_ref,
                                          a.v.llvm_value_ref,
                                          args.as_mut_ptr() as *mut LLVMValueRef,
                                          args.len() as c_uint,
                                          name)) }
        }
    }
    pub fn build_ret(&self, v: Value<'c>) -> Value<'c> {
        unsafe {
            Value(LLVMBuildRet(self.llvm_builder_ref, v.llvm_value_ref))
        }
    }
}

macro_rules! builder_binop {
    ($method:ident, $LLVMMethod:ident) => {
        impl<'c> Builder<'c> {
            pub fn $method(&self, a: Value<'c>, b: Value<'c>, name: Option<&str>) -> Value<'c> {
                let name = c_name(name);
                unsafe {
                    Value($LLVMMethod(self.llvm_builder_ref,
                                      a.llvm_value_ref,
                                      b.llvm_value_ref,
                                      name.as_ptr()))
                }
            }
        }

    }
}

builder_binop!(build_iadd, LLVMBuildAdd);
builder_binop!(build_fadd, LLVMBuildFAdd);
builder_binop!(build_imul, LLVMBuildMul);
builder_binop!(build_fmul, LLVMBuildFMul);
builder_binop!(build_isub, LLVMBuildSub);
builder_binop!(build_fsub, LLVMBuildFSub);
builder_binop!(build_udiv, LLVMBuildUDiv);
builder_binop!(build_sdiv, LLVMBuildSDiv);
builder_binop!(build_fdiv, LLVMBuildFDiv);
builder_binop!(build_and,  LLVMBuildAnd);
builder_binop!(build_or,   LLVMBuildOr);

impl<'c> Builder<'c> {
    pub fn build_not(&self, a: Value<'c>) -> Value<'c> {
        unimplemented!()
    }
    pub fn build_ui_to_fp(&self, a: Value<'c>, t: &Type<'c>) -> Value<'c> {
        unimplemented!()
    }
    pub fn build_icmp(&self, a: Value<'c>, b: Value<'c>, op: llvm_sys::LLVMIntPredicate) -> Value<'c> {
        unimplemented!()
    }
    pub fn build_fcmp(&self, a: Value<'c>, b: Value<'c>, op: llvm_sys::LLVMRealPredicate) -> Value<'c> {
        unimplemented!()
    }
    pub fn build_switch(&self,
                        a: Value<'c>,
                        default: &Block,
                        cases: &[(Value<'c>, &Block<'c>)]) -> Value<'c> {
        unsafe {
            let lswitch = LLVMBuildSwitch(self.llvm_builder_ref,
                                          a.llvm_value_ref,
                                          default.llvm_basic_block_ref,
                                          cases.len() as c_uint);
            for &(v, b) in cases {
                LLVMAddCase(lswitch, v.llvm_value_ref, b.llvm_basic_block_ref);
            }
            Value(lswitch)
        }
    }
}

impl<'m> Module<'m> {
    pub fn new<'c:'m>(name: &str, llvm_context: &Context<'c>) -> Module<'m> {
        let name = CString::new(name).unwrap();
        let mref = unsafe {
            LLVMModuleCreateWithNameInContext(name.as_ptr(),
                                              llvm_context.llvm_context_ref)
        };
        Module { a: PhantomData, llvm_module_ref: mref }
    }
    pub fn get_function(&self, name: &str) -> Option<FunctionPointer<'m>> {
        let s = CString::new(name).unwrap();
        let f = unsafe {
            LLVMGetNamedFunction(self.llvm_module_ref, s.as_ptr())
        };
        if f.is_null() {
            None
        } else {
            Some(Function(f))
        }
    }
    pub fn add_function(&self, name: &str, sig: FunctionType) -> FunctionPointer<'m> {
        let s = CString::new(name).unwrap();
        let f = unsafe {
            LLVMAddFunction(self.llvm_module_ref,
                            s.as_ptr(),
                            sig.t.llvm_type_ref)
        };
        assert!(!f.is_null());
        Function(f)
    }
    pub fn dump(&self) {
        // unsafe {
        //     let mref: llvm_sys::prelude::LLVMModuleRef = (*ctxt.module).as_ptr();
        //     llvm_sys::core::LLVMDumpModule(mref);
        // }
    }
    pub fn verify(&self) -> Result<(), Message> {
        unsafe {
            let mut msg: *mut c_char = mem::uninitialized();
            let ret = llvm_sys::analysis::LLVMVerifyModule(
                self.llvm_module_ref,
                llvm_sys::analysis::LLVMVerifierFailureAction::LLVMReturnStatusAction,
                // llvm_sys::analysis::LLVMVerifierFailureAction::LLVMPrintMessageAction,
                // llvm_sys::analysis::LLVMVerifierFailureAction::LLVMAbortProcessAction,
                &mut msg);
            if ret == 1 {
                Err(Message(msg))
            } else {
                Ok(())
            }
        }
    }
}

mod fun_ctors {
    #![allow(non_snake_case)]
    use super::*;
    use llvm_sys::prelude::*;
    use std::marker::PhantomData;

    pub fn Value<'c>(v: LLVMValueRef) -> Value<'c> {
        Value { a: PhantomData, llvm_value_ref: v }
    }

    pub fn Function<'c>(f: LLVMValueRef) -> FunctionPointer<'c> {
        let r = FunctionPointer { v: Value(f) };
        assert!(r.v.get_type().is_pointer());
        r
    }

    pub fn Context<'c>(c: LLVMContextRef) -> Context<'c> {
        Context { a: PhantomData, llvm_context_ref: c }
    }

    pub fn Type<'c>(t: LLVMTypeRef) -> Type<'c> {
        Type { a: PhantomData, llvm_type_ref: t }
    }

    pub fn FunctionType<'c>(t: LLVMTypeRef) -> FunctionType<'c> {
        FunctionType { t: Type(t) }
    }

    pub fn PointerType<'c>(t: LLVMTypeRef) -> PointerType<'c> {
        PointerType { t: Type(t) }
    }

    pub fn Block<'c>(b: LLVMBasicBlockRef) -> Block<'c> {
        Block { a: PhantomData, llvm_basic_block_ref: b }
    }
}
```
