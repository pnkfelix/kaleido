The `Token` enum is just transcribed from the original tutorial, with more "rustic" names here.

We can choose names without the "tok_" prefix because of how Rust namespaces enum variants. And we can have the variants carry associated data
because Rust has algebraic data types.

```rust
use std::borrow::Cow;
use std::mem;

/// The lexer returns Char for char in "known" operator range [0-255];
/// otherwise one of the other variants for known things.
#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    Char(char),
    EndOfInput,
    /// def command
    Def,
    /// extern command
    Extern,
    /// primary
    Identifier(Cow<'static, str>),
    Number(f64),
}

type Input<'a> = &'a mut Iterator<Item=char>;
```

The sample lexer from the tutorial uses a lot of mutable static data.
I prefer to follow Rust idioms here, so I tried creating a `Lexer` struct
that would carry all of the relevant "global" state.

Then it turned out that much of the global state was built up
locally and could be handed off via the `Token` enum, so
that removed much complexity.

Finally, I decided I wanted to try to encode some session-type-like
static semantics for when the lexer has filled its `last_char`
"buffer" (i.e. it has read the next charater) and when that
"buffer" is empty (i.e. it has processed that character and
accumulated it properly in whatever identifier or other state
that it contributed to. So I defined the logic in terms of a `LexerSession`,
which carries the state of its buffer in its type, and then wrapped
that in a `Lexer` for use by clients who are ignoring the buffer
state.

(The `last_char` and `input` fields are explained further below.)

```rust
pub struct Lexer<'a>(LexerState<'a>);

enum LexerState<'a> {
    Empty(LexerSession<'a, ()>),
    Input(LexerSession<'a, LastChar>),
    Dance, // emulating an old-school option dance
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a mut Iterator<Item=char>) -> Lexer<'a> {
        Lexer(LexerState::Empty(LexerSession::new(input)))
    }

    pub fn next(&mut self) -> Token {
        let l = mem::replace(&mut self.0, LexerState::Dance);
        let (l, c) = match l {
            LexerState::Empty(ls) => ls.get_tok(),
            LexerState::Input(ls) => ls.get_tok(),
            LexerState::Dance => panic!("`Lexer::next` is not re-entrant"),
        };
        self.0 = LexerState::Input(l);
        c
    }
}

struct LexerSession<'a, CS: CharState> {
    input: Input<'a>,
    last_char: CS,
}
```

I have gone through some back-and-forth about how to translate the `last_char`
global state, which was just a `char` in the original tutorial, set to `' '`
at the outset of the program. I played with using just `Option<char>`, but
that complicates things slightly since it is not clear whether the `None`
variant there represents "End of input" or "Have not started yet."

```rust
#[derive(Copy, Clone)]
enum LastChar {
    Char(char),
    End,
}

trait CharState {
    /// Returns true for (1.) whitespace input or (2.) no input yet read.
    fn hungry_for_content(&self) -> bool;

    /// provides char for processing, reading from `i` if necessary
    fn initial(self, i: &mut Input) -> LastChar;
}

impl CharState for () {
    /// Returns true for no input yet read.
    fn hungry_for_content(&self) -> bool {
        true
    }

    /// provides char for processing, reading from `i` if necessary
    fn initial(self, i: &mut Input) -> LastChar {
        match i.next() {
            Some(c) => LastChar::Char(c),
            None => LastChar::End,
        }
    }
}

impl CharState for LastChar {
    /// Returns true for whitespace input.
    fn hungry_for_content(&self) -> bool {
        match *self {
            LastChar::Char(c) => c.is_whitespace(),
            LastChar::End => false,
        }
    }

    /// provides char for processing, reading from `i` if necessary
    fn initial(self, _: &mut Input) -> LastChar {
        self
    }
}

impl LastChar {
    /// Returns true for (1.) whitespace input or (2.) no input yet read.
    fn hungry_for_content(&self) -> bool {
        match *self {
            LastChar::Char(c) => c.is_whitespace(),
            LastChar::End => false,
        }
    }
}

impl<'a> LexerSession<'a, ()> {
    fn new(input: &'a mut Iterator<Item=char>) -> LexerSession<()> {
        LexerSession {
            input: input,
            last_char: (),
        }
    }
}
```

Also, I am adding a `get_char` helper method that both extracts the
next character (if any), updates the internal state stashing that
result, and finally returns it.

(This, like my `fn new` above, is not part of the original tutorial,
but seems to help remove some of the ugliness in the code that
adopting Rust idioms injected.)

```rust
impl<'a, CS:CharState> LexerSession<'a, CS> {
    fn next_char(mut self) -> LexerSession<'a, LastChar> {
        let c = match self.input.next() {
            None => LastChar::End,
            Some(c) => LastChar::Char(c),
        };
        LexerSession {
            input: self.input,
            last_char: c,
        }
    }
}

impl<'a> LexerSession<'a, LastChar> {
    fn get_char(&mut self) -> LastChar {
        let c = match self.input.next() {
            None => LastChar::End,
            Some(c) => LastChar::Char(c),
        };
        self.last_char = c;
        c
    }
}
```

Okay the bulk of the lexer code is dedicated to the body of `gettok`,
which returns the next token.

In the original tutorial text this read from standard-input, but I saw
no reason to not just attach the input stream to the `LexerSession` value
itself. (And rather than use an actual stream, we can just use a
`char` iterator, since IO input stream carry a method that yields a
`char` iterator.

```rust
impl<'a, CS:CharState> LexerSession<'a, CS> {
    fn get_tok(mut self) -> (LexerSession<'a, LastChar>, Token) {
        let mut l = LexerSession {
            last_char: self.last_char.initial(&mut self.input),
            input: self.input
        };

        // skip any whitespace
        while l.last_char.hungry_for_content() {
            l = l.next_char();
        }
```

The above skips whitespace between tokens and tracks the
last extracted input in `self.last_char`.

I am revising the control flow of the presentation
slightly and handling end-of-file first. I thought
doing so would simplify matters, but I am not
100% sure this is actually the case. Anyway, here
is that; it finishes the `get_tok` call if we have
hit EOF, and otherwise binds `c` to the character
we just read.

```rust
        let c = match l.last_char {
            LastChar::End => return (l, Token::EndOfInput),
            LastChar::Char(c) => c,
        };
```

Next we need to recognize identifiers and the builtin keywords.
We do this by recognizing the regexp `[a-zA-Z][a-zA-Z0-9]*`,
building up the string for it if it matches, and returning
the appropriate token for that string when it does.

```rust
        match c {
            c if c.is_alphabetic() => {
                let mut identifier_str = String::new();
                identifier_str.push(c);
                loop {
                    if let LastChar::Char(c) = l.get_char() {
                        if c.is_digit(10) ||
                            c.is_alphabetic() ||
                            ['_'].contains(&c) {
                            identifier_str.push(c);
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }

                if identifier_str == "def" { return (l, Token::Def); }
                if identifier_str == "extern" { return (l, Token::Extern); }
                return (l, Token::Identifier(Cow::Owned(identifier_str)));
            }
```

Numeric values are handled by a similar loop.

```rust
            c if is_numeric(c) => {

                use std::str::FromStr;
                let mut num_str = String::new();
                let mut c = c;
                loop {
                    num_str.push(c);
                    if let LastChar::Char(c2) = l.get_char() {
                        c = c2;
                        if is_numeric(c) { continue; }
                    }
                    break;
                }

                let d = FromStr::from_str(&num_str).unwrap();
                return (l, Token::Number(d));
            }
```

The above implementation contains bugs that were mentioned in the tutorial,
e.g. it does not guard against attempts to parse "1.23.45.67" (though the
Rust `FromStr` method will do a better job of error'ing on those than
the tutorial's `stdtod` call would.

Like the tutorial, we handle comments next.

```rust
            '#' => {
                loop {
                    match l.get_char() {
                        LastChar::Char(c) if c != '\n' && c != '\r' => continue,
                        _ => break,
                    }
                }

                return l.get_tok();
            }

            c => return (l.next_char(), Token::Char(c)),
        }
```

So, we're done; the above defines the returned value for the call.

The rest is just a little helper routine to make the code
for the numeric matching case a little simpler.

```rust
        fn is_numeric(c: char) -> bool {
            c.is_digit(10) || c == '.'
        }
    }
}
```

This is essentially where the original tutorial ends.

But we're not done yet.

In particular, let us make some unit tests, since I am (1.) a
well-meaning SW engineer, and (2.) more than a little concerned about
the various ways I deviated from the original code in my design above.

```rust
#[test]
fn lexsess_empty() {
    assert_eq!(LexerSession::new(&mut "".chars()).get_tok().1,
               Token::EndOfInput);
}

#[test]
fn lexsess_def() {
    assert_eq!(LexerSession::new(&mut "def".chars()).get_tok().1,
               Token::Def);
}

#[test]
fn lexsess_ws_def() {
    assert_eq!(LexerSession::new(&mut "   def".chars()).get_tok().1,
               Token::Def);
}

#[test]
fn lexsess_ws_extern() {
    assert_eq!(LexerSession::new(&mut "   extern".chars()).get_tok().1,
               Token::Extern);
}

#[test]
fn lexsess_ws_extern_ws() {
    assert_eq!(LexerSession::new(&mut "   extern ".chars()).get_tok().1,
               Token::Extern);
}

#[test]
fn lexsess_ws_ident() {
    assert_eq!(LexerSession::new(&mut "   ident ".chars()).get_tok().1,
               Token::Identifier(Cow::Borrowed("ident")));
}

#[test]
fn lexsess_ws_ident_with_digit() {
    assert_eq!(LexerSession::new(&mut "   id3nt ".chars()).get_tok().1,
               Token::Identifier(Cow::Borrowed("id3nt")));
}

#[test]
fn lexsess_ws_ident_with_underscore() {
    assert_eq!(LexerSession::new(&mut "   id_nt ".chars()).get_tok().1,
               Token::Identifier(Cow::Borrowed("id_nt")));
}

#[test]
fn lexsess_ws_zero() {
    assert_eq!(LexerSession::new(&mut "   0 ".chars()).get_tok().1,
               Token::Number(0.0));
}

#[test]
fn lexsess_ws_pi() {
    assert!(match LexerSession::new(&mut "   3.14159 ".chars()).get_tok().1 {
        Token::Number(p) => (p - 3.14159).abs() < 0.00001,
        _ => false,
    });
}

#[test]
fn lexsess_ws_plus() {
    assert_eq!(LexerSession::new(&mut "   + ".chars()).get_tok().1,
               Token::Char('+'));
}

#[test]
fn lexsess_ws_div() {
    assert_eq!(LexerSession::new(&mut "   / ".chars()).get_tok().1,
               Token::Char('/'));
}

// Now for some (maybe) non-obvious corner cases: We do not lex things like `"+="`
// as a single operator; it is lexed instead as two separate tokens: `+` and `=`.

#[test]
fn lexsess_ws_pluseq() {
    let mut input = "  += ".chars();
    let l = LexerSession::new(&mut input);
    let (l, c0) = l.get_tok();
    let (_, c1) = l.get_tok();
    assert_eq!((c0, c1),
               (Token::Char('+'), Token::Char('=')));
}

#[test]
fn lexsess_ws_identplusident() {
    let mut input = "  a+b ".chars();
    let l = LexerSession::new(&mut input);
    let (l, c0) = l.get_tok();
    let (l, c1) = l.get_tok();
    let (_, c2) = l.get_tok();
    assert_eq!((c0, c1, c2),
               (Token::Identifier(Cow::Borrowed("a")),
                Token::Char('+'),
                Token::Identifier(Cow::Borrowed("b"))));
}

#[test]
fn lexsess_ws_def_identopenclose() {
    let mut input = "  def a() ".chars();
    let l = LexerSession::new(&mut input);
    let (l, c0) = l.get_tok();
    let (l, c1) = l.get_tok();
    let (l, c2) = l.get_tok();
    let (_, c3) = l.get_tok();
    assert_eq!((c0, c1, c2, c3),
               (Token::Def,
                Token::Identifier(Cow::Borrowed("a")),
                Token::Char('('),
                Token::Char(')')));
}
```

Finally, here is a repeat of a previous test, but using the
`Lexer` type that we actually expose to the outside world
(that has a more traditional parser interface via a `&mut self`
method rather than using a session type.)

```rust
#[test]
fn lex_ws_def_identopenclose() {
    let mut input = "  def a() ".chars();
    let mut l = Lexer::new(&mut input);
    let c0 = l.next();
    let c1 = l.next();
    let c2 = l.next();
    let c3 = l.next();
    assert_eq!((c0, c1, c2, c3),
               (Token::Def,
                Token::Identifier(Cow::Borrowed("a")),
                Token::Char('('),
                Token::Char(')')));
}
```
