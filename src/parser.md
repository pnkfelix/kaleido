Basic expressions; the original Kaleido tutorial
used an OOP style with a `ExprAST` base class and
a collection of extension classes, but I do not
yet see the point of doing that.

(For example, their base class had no members, just a virtual
destructor, so there's no trait-object API suggesting itself yet
here.)

For that matter, for the purposes of my own local experimentation, I
see no reason to be using a full-fledged grammar (be it LL(1) or
whatever else) at all.  A parenthesis-based S-exp grammar should
suffice for me, so I am going to use that now.

```
Expr ::= Num
      |  Ident
      |  Op
      |  (def Ident (Ident ...) Expr ...)
      |  (extern Ident)
      |  (Expr ...)
```

Maybe in the future I will use a more complex grammar, but
for now I want to stop thinking about parsing and want to
get to the meat of the exercise as soon as possible.

```rust
use ast::{Ident, Proto, Expr, ident};
```

Regardless of the structure of the grammar, I want a standard
interface to the parser that will remain the same even if the language
goes through future changes.

With respect to error handling, I gradually built up the structure
below, where any parse error has an associated `ParseContext`
(which tells us the outermost thing we were trying to parse when
we encountered the error), and a `ParseErrorKind`, which tells us
the type of error we encountered.

 * Note that the `ParseErrorKind` might be a *nested* error,
   i.e. something went wrong during a recursive attempt to parse some
   subform in the grammar (and that this can nest arbitrarily).

 * So to find the "actual" error, one might need to traverse deep into
   the nesting structure. Perhaps I should invert this structure, but
   this is the way it is for now.

```rust
use std::result::Result as StdResult;
use super::lexer::{Lexer, Token};

pub type Result<T> = StdResult<T, ParseError>;

#[derive(PartialEq, Debug)]
pub struct ParseError {
    context: ParseContext,
    kind: ParseErrorKind,
}
#[derive(PartialEq, Debug)]
pub enum ParseErrorKind {
    UnexpectedEndOfInput,
    UnexpectedToken(Token),
    Nested(Box<ParseError>),
}
#[derive(PartialEq, Debug)]
pub enum ParseContext {
    ProtoName(ProtoContext),
    ProtoArg(ProtoContext),
    Expr,
    Exprs,
    Args,
    Def,
    Extern,
    Combination,
}
#[derive(PartialEq, Eq, Debug)]
pub enum ProtoContext {
    Def, Extern,
}
```

Yay, with error handling out of the way, we can focus on the structure
of the parser itself.

This grammar is simple, so all the parser needs is the underlying
lexer and the next token stored in a local cache (since we need to
look-ahead (i.e. "peek") in some context and then actually process the
token we previously peeked at in some other point in the code).

```rust
pub struct Parser<'l> {
    lexer: Lexer<'l>,
    next: Option<Token>,
}

impl<'l> Parser<'l> {
    pub fn new(input: &'l mut Iterator<Item=char>) -> Parser<'l> {
        Parser {
            lexer: Lexer::new(input),
            next: None,
        }
    }
}
```

Since this is a simple S-exp grammar, it *should* be really easy to parse. Let's find out
how easy.

This parser, like any other LL(1) parser, will work by storing one token of look-ahead
and then using that to determine what action to take next.

```rust
impl<'l> Parser<'l> {
    fn clear_next(&mut self) {
        self.next = None;
    }

    fn next(&mut self) -> Token {
        match &mut self.next {
            &mut Some(ref r) => r.clone(),
            x @ &mut None => {
                let t = self.lexer.next();
                *x = Some(t.clone());
                t
            }
        }
    }
}
```

The parser is very simple indeed: expressions are either numbers,
identifiers, or special forms wrapped in parentheses.

Here is an elaborated form of the grammar that more directly corresponds
to the actual code that I wrote below:

```
Expr     ::= Number
Expr     ::= Ident
Expr     ::= Form

Form     ::= '(' 'def' Proto Exprs
Form     ::= '(' 'extern' Proto ')'
Form     ::= '(' Exprs

Proto    ::= Ident Args

Args     ::= '(' Ident ... ')'

Exprs    ::= Expr ... ')'
```

Some quick notes:

 * `FIRST(Expr)` == { Number, Ident, '(' }

 * `FIRST(Form)` == { '(' }

 * `FIRST(Proto)` == { Ident }

 * `FIRST(Args)` == { '(' }

 * `FIRST(Exprs)` == `FIRST(Expr)` UNION { ')' }

The most important detail of the above is the derived `FIRST(Form)`,
because that is what lets us dispatch between the cases of `Expr`.

In principle the value of `FIRST(Exprs)` is also important, since
that is what lets us dispatch between the cases of `Form`, but
I have already somewhat hard-coded the logic there.

 * (The elaborated grammar above is probably not truly LL(1); in
   principle I probably still need to factor it so that the common
   prefix for all of `Form` is pulled out and the dispatch would be on
   the first token of some fresh non-terminal representing the
   distinct suffixes.)

All of the parse implementation methods will be in a single `impl` block.

```rust
impl<'l> Parser<'l> {
```

`parse_expr` dispatches on the first token; each element of
`FIRST(Expr)` corresponds to a distinct alternative of the grammar.

```rust
    pub fn parse_expr(&mut self) -> Result<Expr> {
        let err = |kind| {
            Err(ParseError { context: ParseContext::Expr, kind: kind })
        };
        match self.next() {
            // Expr     ::= Number
            Token::Number(n) => {
                self.clear_next();
                Ok(Expr::Number(n))
            }
            // Expr     ::= Ident
            Token::Identifier(s) => {
                self.clear_next();
                Ok(Expr::Ident(ident(s)))
            }
            t @ Token::Def |
            t @ Token::Extern => return err(ParseErrorKind::UnexpectedToken(t)),
            Token::EndOfInput => return err(ParseErrorKind::UnexpectedEndOfInput),
            // Expr     ::= Form
            Token::Char('(') => self.parse_form(),
            Token::Char(c) => {
                self.clear_next();
                Ok(Expr::Op(c))
            }
        }
    }
```

`parse_form` dispatches on the second token; this is "okay" in terms
of the rules of LL(1) since the first token for `Form` is always
`'('`. The second token is one of
`{ 'def', 'extern' } DISJOINT_UNION FIRST(Exprs)`,
corresponding to each of the three alternatives.

```rust
    fn parse_form(&mut self) -> Result<Expr> {
        assert!(self.next == Some(Token::Char('(')));
        self.clear_next();
        match self.next() {
            Token::Def => {
                // Form     ::= '(' 'def' Proto Exprs
                let err = |kind| {
                    Err(ParseError { context: ParseContext::Def, kind: kind })
                };
                self.clear_next();
                let p = match self.parse_proto(ProtoContext::Def) {
                    Ok(p) => p,
                    Err(error) => return err(ParseErrorKind::Nested(Box::new(error))),
                };
                let exprs = match self.parse_exprs() {
                    Ok(es) => es,
                    Err(error) => return err(ParseErrorKind::Nested(Box::new(error))),
                };
                Ok(Expr::Def(p, exprs))
            }
            Token::Extern => {
                // Form     ::= '(' 'extern' Proto ')'
                let err = |kind| {
                    Err(ParseError { context: ParseContext::Extern, kind: kind })
                };
                self.clear_next();
                let p = match self.parse_proto(ProtoContext::Extern) {
                    Ok(p) => p,
                    Err(error) => return err(ParseErrorKind::Nested(Box::new(error))),
                };
                match self.next() {
                    Token::Char(')') => {
                        self.clear_next();
                        Ok(Expr::Extern(p))
                    }
                    t => return err(ParseErrorKind::UnexpectedToken(t)),
                }
            }
            _ => {
                // Form     ::= '(' Exprs
                let err = |kind| {
                    Err(ParseError { context: ParseContext::Combination, kind: kind })
                };
                let exprs = match self.parse_exprs() {
                    Ok(es) => es,
                    Err(error) => return err(ParseErrorKind::Nested(Box::new(error))),
                };
                Ok(Expr::Combine(exprs))
            }
        }
    }
```

`parse_proto` does not need to dispatch.

```rust
    fn parse_proto
(&mut self, pc: ProtoContext) -> Result<Proto> {
        // Proto    ::= Ident Args
        let err = |kind| {
            Err(ParseError { context: ParseContext::ProtoName(pc), kind: kind })
        };
        let name = match self.next() {
            Token::Identifier(s) => ident(s),
            t => return err(ParseErrorKind::UnexpectedToken(t)),
        };
        self.clear_next();
        let args = match self.parse_args() {
            Ok(args) => args,
            Err(error) => return err(ParseErrorKind::Nested(Box::new(error))),
        };
        Ok(Proto { name: name, args: args })
    }
```

`parse_args` does not need to dispatch, at least not to choose an
immediate alternative.

(Where it *does* need to dipatch is in deciding whether to end the
loop; again, strictly speaking a true LL(1) form of the grammar would
probably need to elaborate on operators like the `...` that I used in
my grammars above.)

```rust
    fn parse_args(&mut self) -> Result<Vec<Ident>> {
        // Args     ::= '(' Ident ... ')'
        let err = |kind| {
            Err(ParseError { context: ParseContext::Args, kind: kind })
        };
        match self.next() {
            Token::Char('(') => (),
            t => return err(ParseErrorKind::UnexpectedToken(t)),
        }
        let mut v = Vec::new();
        loop {
            self.clear_next();
            if let Token::Char(')') = self.next() {
                self.clear_next();
                return Ok(v);
            }
            let arg = match self.next() {
                Token::Identifier(s) => ident(s),
                t => return err(ParseErrorKind::UnexpectedToken(t)),
            };
            v.push(arg);
        }
    }
```

`parse_exprs` is analogous to `parse_arg` -- it has only one
alternative, but it does contain a Kleene closure form and thus needs
to accumulate the expressions there.

```rust
    fn parse_exprs(&mut self) -> Result<Vec<Expr>> {
        // Exprs    ::= Expr ... ')'
        let err = |kind| {
            Err(ParseError { context: ParseContext::Exprs, kind: kind })
        };
        let mut v = Vec::new();
        loop {
            if let Token::Char(')') = self.next() {
                self.clear_next();
                return Ok(v);
            }
            let e = match self.parse_expr() {
                Ok(e) => e,
                Err(error) => return err(ParseErrorKind::Nested(Box::new(error))),
            };
            v.push(e);
        }
    }
}
```

Test cases, written from scratch. (Maybe later I will look at the
official tutorial source to see if it shows any unit tests of its own,
but my memory is that the tutorial code was pretty light with respect
to unit testing.)

```rust
#[cfg(test)]
use inputs::*;

#[test]
fn parse_empty() {
    let mut input = "".chars();
    assert_eq!(Parser::new(&mut input).parse_expr(),
               Err(ParseError {
                   context: ParseContext::Expr,
                   kind: ParseErrorKind::UnexpectedEndOfInput,
               }));
}

#[test]
fn parse_num_one() {
    let mut input = "1".chars();
    assert_eq!(Parser::new(&mut input).parse_expr(),
               Ok(Expr::Number(1.0)));
}

#[test]
fn parse_num_ten() {
    let mut input = "10".chars();
    assert_eq!(Parser::new(&mut input).parse_expr(),
               Ok(Expr::Number(10.0)));
}

#[test]
fn parse_ident_foo() {
    let mut input = " foo ".chars();
    assert_eq!(Parser::new(&mut input).parse_expr(),
               Ok(Expr::Ident(ident("foo"))));
}

#[test]
fn parse_extern_foo() {
    let mut input = EXTERN_FOO.chars();
    assert_eq!(Parser::new(&mut input).parse_expr(),
               Ok(Expr::Extern(Proto { name: ident("foo"),
                                       args: vec![] })));
}

#[test]
fn parse_args() {
    let mut input = "(a b)".chars();
    assert_eq!(Parser::new(&mut input).parse_args(),
               Ok(vec![ident("a"), ident("b")]));
}

#[test]
fn parse_proto() {
    let mut input = "foo (a b)".chars();
    assert_eq!(Parser::new(&mut input).parse_proto(ProtoContext::Extern),
               Ok(Proto { name: ident("foo"),
                          args: vec![ident("a"), ident("b")] }));
}

#[test]
fn parse_def_id() {
    let mut input = DEF_ID.chars();
    let e = Expr::Def(
        Proto { name: ident("id"), args: vec![ident("a")] },
        vec![Expr::Ident(ident("a"))]);
    assert_eq!(Parser::new(&mut input).parse_expr(), Ok(e));
}

#[test]
fn parse_mul() {
    let mut input = "                                   (* a b)             ".chars();
    let e = Expr::Combine(vec![Expr::Op('*'),
                               Expr::Ident(ident("a")),
                               Expr::Ident(ident("b"))]);

    assert_eq!(Parser::new(&mut input).parse_expr(), Ok(e));
}

#[test]
fn parse_nested_mul() {
    let mut input = "                              (* 2 (* a b))            ".chars();
    let e = Expr::Combine(vec![Expr::Op('*'),
                               Expr::Number(2.0),
                               Expr::Combine(vec![Expr::Op('*'),
                                                  Expr::Ident(ident("a")),
                                                  Expr::Ident(ident("b"))])]);

    assert_eq!(Parser::new(&mut input).parse_expr(), Ok(e));
}

#[test]
fn parse_big_expr() {
    let mut input = "                (+ (* a a) (+ (* 2 (* a b)) (* b b)))  ".chars();
    let e =
        Expr::Combine(
            vec![Expr::Op('+'),
                 Expr::Combine(
                     vec![Expr::Op('*'),
                          Expr::Ident(ident("a")),
                          Expr::Ident(ident("a"))]),
                 Expr::Combine(
                     vec![Expr::Op('+'),
                          Expr::Combine(
                              vec![Expr::Op('*'),
                                   Expr::Number(2.0),
                                   Expr::Combine(vec![Expr::Op('*'),
                                                      Expr::Ident(ident("a")),
                                                      Expr::Ident(ident("b"))])]),
                          Expr::Combine(
                              vec![Expr::Op('*'),
                                   Expr::Ident(ident("b")),
                                   Expr::Ident(ident("b"))])])]);

    assert_eq!(Parser::new(&mut input).parse_expr(), Ok(e));
}

#[test]
fn parse_def_foo() {
    let mut input = DEF_FOO.chars();
    let e = Expr::Def(
        Proto { name: ident("foo"), args: vec![ident("a"), ident("b")] },
        vec![Expr::Combine(
            vec![Expr::Op('+'),
                 Expr::Combine(
                     vec![Expr::Op('*'),
                          Expr::Ident(ident("a")),
                          Expr::Ident(ident("a"))]),
                 Expr::Combine(
                     vec![Expr::Op('+'),
                          Expr::Combine(
                              vec![Expr::Op('*'),
                                   Expr::Number(2.0),
                                   Expr::Combine(vec![Expr::Op('*'),
                                                      Expr::Ident(ident("a")),
                                                      Expr::Ident(ident("b"))])]),
                          Expr::Combine(
                              vec![Expr::Op('*'),
                                   Expr::Ident(ident("b")),
                                   Expr::Ident(ident("b"))])])])]);

    assert_eq!(Parser::new(&mut input).parse_expr(), Ok(e));
}
```
