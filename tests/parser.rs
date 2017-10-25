#[macro_use]
extern crate lexpar;

use lexpar::lexer::Span;
use lexpar::parser::ParseError;

macro_rules! iter {
    ( $($e: expr),* ) => { Box::new(vec![ $($e),* ].into_iter()) }
}

#[derive(Debug, Clone, PartialEq)]
enum Kw {
    Fn
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Ident(String),
    Integer(i32),
    Keyword(Kw),
    LParen,
    RParen,
    Arrow
}

use self::Token::*;

#[test]
fn parser1_ok_eof_unexpected() {
    const EXM_STR: &'static str = "!";
    let parse = |iter: Box<Iterator<Item = (Span, Token)>>| {
        parse_rules! {
            term: (Span, Token);

            entry: String => {
                [(_, Ident(name)), (_, Ident(a))] => {
                    format!("{}{}{}", name, a, EXM_STR)
                }
            }
        }

        entry(&mut iter.peekable())
    };

    assert_eq! {
        parse(iter![
            (Span::new(1, 2, 3), Ident("hi".to_owned())),
            (Span::new(1, 2, 3), Ident("world".to_owned()))
        ]),
        Ok(String::from("hiworld!"))
    }

    assert_eq! {
        parse(iter![(Span::new(1, 2, 3), Ident("hi".to_owned()))]),
        Err(ParseError::Eof)
    }

    assert_eq! {
        parse(iter![
            (Span::new(1, 2, 3), Ident("hi".to_owned())),
            (Span::new(1, 2, 3), Integer(123))
        ]),
        Err(ParseError::Unexpected((Span::new(1, 2, 3), Integer(123))))
    }
}

#[test]
fn parser2_nonterm_call() {
    let parse = |iter: Box<Iterator<Item = Token>>| {
        parse_rules! {
            term: Token;

            ident: String => {
                [Ident(name), Ident(a)] => {
                    name + a.as_str() + "I"
                }
            },
            entry: String => {
                [Ident(name), Ident(a), res: ident, Integer(123)] => {
                    res? + name.as_str() + a.as_str() + "E"
                }
            }
        }

        entry(&mut iter.peekable())
    };

    assert_eq! {
        parse(iter![
            Ident("hi".to_owned()),
            Ident("world".to_owned()),
            Ident("a".to_owned()),
            Ident("b".to_owned()),
            Integer(123)
        ]),
        Ok(String::from("abIhiworldE"))
    }
}

#[test]
fn parser3_epsilon_and_trailing_commas() {
    let parse = |iter: Box<Iterator<Item = Token>>| {
        parse_rules! {
            term: Token;

            eps: String => {
                [@] => {
                    String::from("eps")
                }
            },
            i: String => {
                [Ident(name), Ident(_), p: eps] => {
                    name + "I" + &p?
                },
            },
            e: String => {
                [Ident(name), Ident(a), res: i, Integer(123)] => {
                    res? + name.as_str() + a.as_str() + "E"
                },
                [Integer(_)] => {
                    String::from("arm 2")
                }
            },
        }

        e(&mut iter.peekable())
    };

    assert_eq! {
        parse(iter![
            Ident("hi".to_owned()),
            Ident("world".to_owned()),
            Ident("a".to_owned()),
            Ident("b".to_owned()),
            Integer(123)
        ]),
        Ok(String::from("aIepshiworldE"))
    }

    assert_eq! {
        parse(iter![
            Integer(123)
        ]),
        Ok(String::from("arm 2"))
    }
}

#[test]
fn parser4_custom_handler() {
    let parse = |iter: Box<Iterator<Item = Token>>| {
        parse_rules! {
            term: Token;

            i: Vec<String> => |iter| {
                let mut params = Vec::new();

                // while let Some(Ident(name)) = iter.peek().map(|peek| peek.clone()) {
                //     params.push(name);
                //     iter.next();
                // }

                // This variant should be more efficient since it does not clone a string.
                while let Some(&Ident(_)) = iter.peek() {
                    if let Ident(name) = iter.next().unwrap() {
                        params.push(name);
                    }
                }

                Ok(params)
            },
            e: Vec<String> => {
                [Keyword(Kw::Fn), Ident(name), params: i, Arrow] => {
                    let mut idents: Vec<String> = params?;
                    idents.insert(0, name);
                    idents
                }
            }
        }

        e(&mut iter.peekable())
    };

    assert_eq! {
        parse(iter![
            Keyword(Kw::Fn),
            Ident("f".to_owned()),
            Ident("a".to_owned()),
            Ident("b".to_owned()),
            Ident("c".to_owned()),
            Arrow
        ]),
        Ok(vec![
            String::from("f"),
            String::from("a"),
            String::from("b"),
            String::from("c")
        ])
    }
}

#[test]
fn parser5_nonterm_as_first_rule() {
    fn parse(iter: Box<Iterator<Item = Token>>) -> Result<String, ParseError<Token>> {
        parse_rules! {
            term: Token;

            wrong: String => {
                [Integer(_), Ident(a)] => {
                    a
                }
            },
            right: String => {
                [Ident(name), Ident(a)] => {
                    name + a.as_str() + "I"
                }
            },
            e: String => {
                [res: wrong, Ident(name), Ident(a), Integer(123)] => {
                    res? + name.as_str() + a.as_str() + "E"
                },
                [res: right, Ident(name), Ident(a), Integer(123)] => {
                    res? + name.as_str() + a.as_str() + "E"
                }
            }
        }

        e(&mut iter.peekable())
    }

    assert_eq! {
        parse(iter![
            Ident("hi".to_owned()),
            Ident("world".to_owned()),
            Ident("a".to_owned()),
            Ident("b".to_owned()),
            Integer(123)
        ]),
        Ok(String::from("hiworldIabE"))
    }
}

#[test]
fn parser6_recursive_grammar() {
    let parse = |iter: Box<Iterator<Item = Token>>| {
        parse_rules! {
            term: Token;

            ident: String => {
                [Ident(name)] => {
                    format!("*{}*", name)
                }
            },
            expr: String => {
                [LParen, ex: expr, RParen] => { ex? },
                [id: ident] => { id? },
                [Integer(n)] => { n.to_string() }
            }
        }

        expr(&mut iter.peekable())
    };

    assert_eq! {
        parse(iter![Ident(String::from("foo"))]),
        Ok(String::from("*foo*"))
    }

    assert_eq! {
        parse(iter![LParen, Ident(String::from("foo")), RParen]),
        Ok(String::from("*foo*"))
    }

    assert_eq! {
        parse(iter![LParen, Integer(-1), RParen]),
        Ok(String::from("-1"))
    }

    assert_eq! {
        parse(iter![
            LParen,
            LParen,
            LParen,
            Ident(String::from("foo")),
            RParen,
            RParen,
            RParen
        ]),
        Ok(String::from("*foo*"))
    }

    // Disbalanced parentheses
    assert_eq! {
        parse(iter![
            LParen,
            LParen,
            LParen,
            Ident(String::from("foo")),
            RParen,
            RParen
        ]),
        Err(ParseError::Eof)
    }
}

#[test]
fn parser7_kleene_star() {
    let parse = |iter: Box<Iterator<Item = Token>>| {
        parse_rules! {
            term: Token;

            expr: String => {
                [Integer(n), ex: expr] => {
                    println!("hi");
                    format!("{} {}", n, ex?)
                },
                [@] => { String::new() }
            }
        }

        expr(&mut iter.peekable())
    };

    assert_eq! {
        parse(iter![
            Integer(1),
            Integer(5),
            Integer(42),
            Integer(666)
        ]),
        Ok(String::from("1 5 42 666"))
    }
}
