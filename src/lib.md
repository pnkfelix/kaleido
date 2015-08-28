```rust
#![feature(into_cow, slice_patterns)]

extern crate llvm;
extern crate llvm_sys;

pub const FIB_PROG: &'static str = r#"# Compute the x'th fibonacci number.
(def fib (x)
  (if (< x 3)
    1
    (+ (fib (- x 1) (fib (- x 2))))))

# This expression will compute the 40th number.
(fib 40)
"#;

pub const EXTERN_PROG: &'static str = r#"
(extern sin(arg))
(extern cos(arg))
(extern atan2(arg1 arg2))

(atan2 (sin .4) (cos42))
"#;

#[test]
fn it_works() {
}

pub mod ast;
#[cfg(test)]
mod inputs;
pub mod lexer;
pub mod parser;
pub mod codegen;
```
