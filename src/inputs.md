```rust
pub type Code = &'static str;

pub const EXTERN_FOO: Code = " (extern foo ())";
pub const DEF_ID: Code = " (def id (a) a) ";
pub const DEF_FOO: Code =
    " (def foo (a b) (+ (* a a) (+ (* 2 (* a b)) (* b b)))) ";
```
