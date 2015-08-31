```rust
use ast::{Expr, Ident, IntoExpr, Proto, ToExpr, ident};

pub struct Input {
    pub str: &'static str,
    pub ast: Expr,
}

macro_rules! inputs {
    ([$collected:ident; $count:expr] =
     $(fn $id:ident { $str:expr, $ast:expr })*) => {
        pub const $collected: [fn () -> Input; $count] =
            [$($id),*];

        $(pub fn $id() -> Input {
            Input {
                str: $str,
                ast: $ast,
            }
        }
          )*
    }
}

macro_rules! args { [$($e:expr),*] => { vec![$($e.to_expr()),*] } }

fn abc() -> (Ident, Ident, Ident) { (ident("a"), ident("b"), ident("c")) }

inputs!
([COLLECTED; 9] =

 fn extern_foo {
     " (extern foo0 ())",
     Expr::Extern(Proto { name: ident("foo0"), args: vec![] }) }

 fn def_id {
     " (def id (a) a) ",
     Expr::Def(
         Proto { name: ident("id"), args: vec![ident("a")] },
         vec![Expr::Ident(ident("a"))])
 }

 fn def_one_two_x {
     " (def one_two_x (z) (+ 1 (+ 2 z))) ",
     Expr::Def(
         Proto { name: ident("one_two_x"), args: vec![ident("z")] },
         vec![add(1.0, add(2.0, "z"))])
 }

 fn def_discrim {
     " (def discrim (a b c) (- (* b b) (* 4 (* a c)))) ",
     { let (a,b,c) = abc();
       Expr::Def(
           Proto { name: ident("discrim"),
                   args: vec![a.clone(), b.clone(), c.clone()] },
           vec![sub(mul(b.clone(),b), mul(4.0, mul(a, c)))]) }
 }

 fn def_quad_root_a {
     "(def quad_root_a (a b c)
          (extern sqrt (a))
          (extern discrim (a b c))
          (/ (+ (- b) (sqrt (discrim a b c))) (* 2.0 a))) ",
     {
         let (a,b,c) = abc();
         let abc = vec![a.clone(), b.clone(), c.clone()];
         Expr::Def(
             Proto { name: ident("quad_root_a"), args: abc.clone() },
             vec![
                 Expr::Extern(Proto { name: ident("sqrt"), args: vec![a.clone()] }),
                 Expr::Extern(Proto { name: ident("discrim"), args: abc.clone(), }),
                 div(add(neg(b.clone()), Expr::Combine(
                     args!["sqrt", Expr::Combine(args!["discrim", a, b, c])])),
                     mul(2.0, a))])
     }
 }

 fn def_foo {
     DEF_FOO_BREAKDOWN[0],
     Expr::Def(
         Proto { name: ident("foo"), args: vec![ident("a"), ident("b")] },
         vec![expr_big().ast])
 }

 // this is ast for "                (+ (* a a) (+ (* 2 (* a b)) (* b b)))  "
 fn expr_big {
     DEF_FOO_BREAKDOWN[1],
     add(mul(ident("a"), ident("a")),
         add(mul(2.0, mul(ident("a"), ident("b"))),
             mul(ident("b"), ident("b"))))
 }

 fn expr_nested_mul {
     DEF_FOO_BREAKDOWN[2],
     mul(2.0, mul(ident("a"), ident("b")))
 }

 fn expr_mul {
     DEF_FOO_BREAKDOWN[3],
     mul(ident("a"), ident("b"))
 }

 );

type Code = &'static str;
const DEF_FOO_BREAKDOWN: [Code; 4] =
    [" (def foo (a b) (+ (* a a) (+ (* 2 (* a b)) (* b b)))) ",
     "                (+ (* a a) (+ (* 2 (* a b)) (* b b)))  ",
     "                              (* 2 (* a b))            ",
     "                                   (* a b)             ",
     ];

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
```
