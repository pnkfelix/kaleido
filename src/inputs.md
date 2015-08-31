```rust
use ast::{Expr, Ident, IntoExpr, Proto, ToExpr, ident};

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

macro_rules! args { [$($e:expr),*] => { vec![$($e.to_expr()),*] } }

pub fn def_id() -> Input {
    Input {
        str: " (def id (a) a) ",
        ast: Expr::Def(
            Proto { name: ident("id"), args: vec![ident("a")] },
            vec![Expr::Ident(ident("a"))]),
    }
}

fn abc() -> (Ident, Ident, Ident) { (ident("a"), ident("b"), ident("c")) }

pub fn def_discrim() -> Input {
    let (a,b,c) = abc();
    Input {
        str: " (def discrim (a b c) (- (* b b) (* 4 (* a c)))) ",
        ast: Expr::Def(
            Proto { name: ident("discrim"), args: vec![a.clone(), b.clone(), c.clone()] },
            vec![sub(mul(b.clone(),b), mul(4.0, mul(a, c)))])
    }
}

pub fn def_quad_root_a() -> Input {
    let (a,b,c) = abc();
    let abc = vec![a.clone(), b.clone(), c.clone()];
    Input {
        str: "(def quad_root_a (a b c)
                 (extern sqrt (a))
                 (extern discrim (a b c))
                 (/ (+ (- b) (sqrt (discrim a b c))) (* 2.0 a))) ",
        ast: Expr::Def(
            Proto { name: ident("quad_root_a"), args: abc.clone() },
            vec![
                Expr::Extern(Proto { name: ident("sqrt"), args: vec![a.clone()] }),
                Expr::Extern(Proto { name: ident("discrim"), args: abc.clone(), }),
                div(add(neg(b.clone()), Expr::Combine(
                    args!["sqrt", Expr::Combine(args!["discrim", a, b, c])])),
                    mul(2.0, a))])
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

fn neg<E1:IntoExpr>(a: E1) -> Expr {
    Expr::Combine(vec![Expr::Op('-'), a.into_expr()])
}

fn binop<E1:IntoExpr, E2:IntoExpr>(op: char, a: E1, b: E2) -> Expr {
    Expr::Combine(vec![Expr::Op(op), a.into_expr(), b.into_expr()])
}

fn add<E1:IntoExpr, E2:IntoExpr>(a: E1, b: E2) -> Expr { binop('+', a, b) }

fn sub<E1:IntoExpr, E2:IntoExpr>(a: E1, b: E2) -> Expr { binop('-', a, b) }

fn mul<E1:IntoExpr, E2:IntoExpr>(a: E1, b: E2) -> Expr { binop('*', a, b) }

fn div<E1:IntoExpr, E2:IntoExpr>(a: E1, b: E2) -> Expr { binop('/', a, b) }

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
