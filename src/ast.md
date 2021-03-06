```rust
use std::borrow::{Cow, IntoCow};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ident { pub name: Cow<'static, str> }

pub fn ident<S:IntoCow<'static, str>>(s: S) -> Ident {
    Ident { name: s.into_cow() }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Proto { pub name: Ident, pub args: Vec<Ident> }

#[derive(Clone, PartialEq, Debug)]
pub enum Expr {
    Number(f64),
    Ident(Ident),
    Op(char),
    Def(Proto, Vec<Expr>),
    Extern(Proto),
    Combine(Vec<Expr>),
}

pub trait IntoExpr { fn into_expr(self) -> Expr; }

impl IntoExpr for Expr {
    fn into_expr(self) -> Expr { self }
}
impl IntoExpr for f64 {
    fn into_expr(self) -> Expr { Expr::Number(self) }
}
impl IntoExpr for Ident {
    fn into_expr(self) -> Expr { Expr::Ident(self) }
}
impl IntoExpr for &'static str {
    fn into_expr(self) -> Expr { Expr::Ident(ident(self)) }
}

pub trait ToExpr { fn to_expr(&self) -> Expr; }
impl<T:Clone+IntoExpr> ToExpr for T {
    fn to_expr(&self) -> Expr { self.clone().into_expr() }
}

impl Expr {
    pub fn has_free_variables(&self, bound: &[Ident]) -> bool {
        match *self {
            Expr::Number(..) |
            Expr::Op(..) |
            Expr::Extern(..) => false,
            Expr::Ident(ref i) => !bound.contains(i),
            Expr::Def(ref proto, ref body) => {
                let mut subbound = proto.args.clone();
                subbound.push(proto.name.clone());
                body.iter().any(|e| e.has_free_variables(&subbound))
            }
            Expr::Combine(ref exprs) =>
                exprs.iter().any(|e| e.has_free_variables(bound)),
        }
    }
}
```
