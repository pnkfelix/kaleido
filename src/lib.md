```rust
extern crate llvm;

const FIB_PROG: &'static str = r#"# Compute the x'th fibonacci number.
def fib(x)
  if x < 3 then
    1
  else
    fib(x-1) + fib(x-2)

# This expression will compute the 40th number.
fib(40)
"#;

const EXTERN_PROG: &'static str = r#"
extern sin(arg);
extern cos(arg);
extern atan2(arg1 arg2);

atan2(sin(.4), cos(42))
"#;

#[test]
fn it_works() {
}

mod lexer;
```
