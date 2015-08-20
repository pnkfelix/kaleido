```rust
use std::borrow::Cow;

#[derive(PartialEq, Eq, Debug)]
pub struct Ident { pub name: Cow<'static, str> }

#[derive(PartialEq, Eq, Debug)]
pub struct Proto { pub name: Ident, pub args: Vec<Ident> }

#[derive(PartialEq, Debug)]
pub enum Expr {
    Number(f64),
    Ident(Ident),
    Op(char),
    Def(Proto, Vec<Expr>),
    Extern(Proto),
    Combine(Vec<Expr>),
}
```
