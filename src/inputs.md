```rust
use ast::{Expr, IntoExpr, Proto, ident};

pub struct Input {
    pub str: &'static str,
    pub ast: Expr,
}

pub fn extern_foo() -> Input {
    Input {
        str: " (extern foo ())",
        ast: Expr::Extern(Proto { name: ident("foo"), args: vec![] }),
    }
}

pub fn def_id() -> Input {
    Input {
        str: " (def id (a) a) ",
        ast: Expr::Def(
            Proto { name: ident("id"), args: vec![ident("a")] },
            vec![Expr::Ident(ident("a"))]),
    }
}

type Code = &'static str;
const DEF_FOO_BREAKDOWN: [Code; 4] =
    [" (def foo (a b) (+ (* a a) (+ (* 2 (* a b)) (* b b)))) ",
     "                (+ (* a a) (+ (* 2 (* a b)) (* b b)))  ",
     "                              (* 2 (* a b))            ",
     "                                   (* a b)             ",
     ];

pub fn def_foo() -> Input {
    let str = DEF_FOO_BREAKDOWN[0];
    let ast = Expr::Def(
        Proto { name: ident("foo"), args: vec![ident("a"), ident("b")] },
        vec![expr_big().ast]);

    Input { str: str, ast: ast, }
}

fn add<E1:IntoExpr, E2:IntoExpr>(a: E1, b: E2) -> Expr {
    Expr::Combine(vec![Expr::Op('+'), a.into_expr(), b.into_expr()])
}

fn mul<E1:IntoExpr, E2:IntoExpr>(a: E1, b: E2) -> Expr {
    Expr::Combine(vec![Expr::Op('*'), a.into_expr(), b.into_expr()])
}

/// this is ast for "                (+ (* a a) (+ (* 2 (* a b)) (* b b)))  "
pub fn expr_big() -> Input {
    let str = DEF_FOO_BREAKDOWN[1];
    let ast = add(mul(ident("a"), ident("a")),
                  add(mul(2.0, mul(ident("a"), ident("b"))),
                      mul(ident("b"), ident("b"))));

    Input { str: str, ast: ast, }
}

pub fn expr_nested_mul() -> Input {
    let str = DEF_FOO_BREAKDOWN[2];
    let ast = mul(2.0, mul(ident("a"), ident("b")));
    Input { str: str, ast: ast }
}

pub fn expr_mul() -> Input {
    let str = DEF_FOO_BREAKDOWN[3];
    let ast = mul(ident("a"), ident("b"));
    Input { str: str, ast: ast }
}
```
