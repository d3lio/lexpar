#[macro_use]
extern crate lexpar;

use lexpar::lexer::Span;
use lexpar::parser::{UnshiftIter, ParseError};

macro_rules! iter {
    ( $($e: expr),* ) => { Box::new(vec![ $($e),* ].into_iter()) }
}

#[derive(Debug, PartialEq)]
enum Kw {
    Fn
}

#[derive(Debug, PartialEq)]
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

        entry(&mut UnshiftIter::from(iter.peekable()))
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

        entry(&mut UnshiftIter::from(iter.peekable()))
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

        e(&mut UnshiftIter::from(iter.peekable()))
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

        e(&mut UnshiftIter::from(iter.peekable()))
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
    fn parse<I>(iter: I) -> Result<String, ParseError<Token>> where I: Iterator<Item = Token> {
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

        e(&mut UnshiftIter::from(iter.peekable()))
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

        expr(&mut UnshiftIter::from(iter.peekable()))
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

mod looping {
    use super::*;

    #[test]
    fn parser7_kleene_star() {
        let parse = |iter: Box<Iterator<Item = Token>>| {
            parse_rules! {
                term: Token;

                expr: String => {
                    [Ident(name), Integer(n), ex: expr] => {
                        format!("{}:{}, {}", name, n, ex?)
                    },
                    [@] => { String::new() }
                }
            }

            expr(&mut UnshiftIter::from(iter.peekable()))
        };

        assert_eq! {
            parse(iter![
                Ident(String::from("one")),
                Integer(1),
                Ident(String::from("five")),
                Integer(5),
                Ident(String::from("life")),
                Integer(42),
                Ident(String::from("devil")),
                Integer(666)
            ]),
            Ok(String::from("one:1, five:5, life:42, devil:666, "))
        }

        assert_eq! {
            parse(iter![
                Integer(1),
                Integer(5),
                Integer(42),
                Integer(666)
            ]),
            Ok(String::from(""))
        }

        assert_eq! {
            parse(iter![
                Ident(String::from("one")),
                Integer(1),
                Integer(5)
            ]),
            Ok(String::from("one:1, "))
        }

        assert_eq! {
            parse(iter![
                Ident(String::from("one"))
            ]),
            Err(ParseError::Eof)
        }
    }

    macro_rules! assert_args {
        ($parse: ident) => {
            assert_eq! {
                $parse(iter![
                    Keyword(Kw::Fn),
                    Ident(String::from("my_fn")),
                    LParen,
                    Ident(String::from("one")),
                    Integer(1),
                    Ident(String::from("five")),
                    Integer(5),
                    RParen
                ]),
                Ok(String::from("my_fn(one = 1, five = 5)"))
            }

            assert_eq! {
                $parse(iter![
                    Keyword(Kw::Fn),
                    Ident(String::from("my_fn")),
                    LParen,
                    RParen
                ]),
                Ok(String::from("my_fn()"))
            }

            assert_eq! {
                $parse(iter![
                    Keyword(Kw::Fn),
                    Ident(String::from("my_fn")),
                    Ident(String::from("one")),
                    Integer(1),
                    Ident(String::from("five")),
                    Integer(5),
                    RParen
                ]),
                Err(ParseError::Unexpected(Ident(String::from("one"))))
            }
        }
    }

    #[test]
    fn parser8_fn_args() {
        let parse = |iter: Box<Iterator<Item = Token>>| {
            parse_rules! {
                term: Token;

                args: Vec<(String, String)> => {
                    [Ident(name), Integer(n), v: args] => {
                        let mut args = v?;
                        args.push((name, n.to_string()));
                        args
                    },
                    [@] => { Vec::new() }
                },

                expr: String => {
                    [Keyword(Kw::Fn), Ident(fn_name), LParen, v: args, RParen] => {
                        let args = v?.into_iter().rev().fold(String::new(), |acc, arg| {
                            format!("{}, {} = {}", acc, arg.0, arg.1)
                        });
                        format!("{}({})", fn_name, if args.len() > 2 { &args[2..] } else { &args })
                    }
                }
            }

            expr(&mut UnshiftIter::from(iter.peekable()))
        };

        assert_args!(parse);
    }

    #[test]
    fn parser9_fold_fn_args() {
        let parse = |iter: Box<Iterator<Item = Token>>| {
            parse_rules! {
                term: Token;

                #[fold(args)]
                args: Vec<(String, String)> => {
                    [Ident(name), Integer(n)] => {
                        args.push((name, n.to_string()));
                        args
                    },
                    [@] => { Vec::new() }
                },

                expr: String => {
                    [Keyword(Kw::Fn), Ident(fn_name), LParen, v: args, RParen] => {
                        let args = v?.into_iter().fold(String::new(), |acc, arg| {
                            format!("{}, {} = {}", acc, arg.0, arg.1)
                        });
                        format!("{}({})", fn_name, if args.len() > 2 { &args[2..] } else { &args })
                    }
                }
            }

            expr(&mut iter.peekable().into())
        };

        assert_args!(parse);
    }
}

mod precedence {
    #[allow(dead_code)]
    #[derive(Debug, PartialEq)]
    enum Token {
        Integer(i32),
        LParen,
        RParen,

        Add,
        Sub,
        Mul,
        Div,
        Not,
        Eq,
        NotEq
    }

    use self::Token::*;

    #[test]
    fn parser9_binop_infix_precedence_syntax() {
        let parse = |iter: Box<Iterator<Item = Token>>| {
            parse_rules! {
                term: Token;

                #[binop(infix)]
                binop: i32 => expr: i32 where precedence: u32 => |lhs, rhs| {
                    &Eq | 0 => (lhs == rhs) as i32,
                    &NotEq | 0 => (lhs != rhs) as i32,
                    &Add | 1 => lhs + rhs,
                    &Sub | 1 => lhs - rhs,
                    &Mul | 2 => lhs * rhs,
                    &Div | 2 => lhs / rhs,
                },

                expr: i32 => {
                    [Integer(a)] => a,
                    [LParen, binop: binop, RParen] => binop?
                }
            }

            binop(&mut iter.peekable().into())
        };

        // 1 + 3 * 5
        assert_eq! {
            parse(iter![
                Integer(1),
                Add,
                Integer(3),
                Mul,
                Integer(5)
            ]),
            Ok(16)
        }

        // (1 + 3) * 5
        assert_eq! {
            parse(iter![
                LParen,
                Integer(1),
                Add,
                Integer(3),
                RParen,
                Mul,
                Integer(5)
            ]),
            Ok(20)
        }

        // 3 * 4 / 6
        assert_eq! {
            parse(iter![
                Integer(3),
                Mul,
                Integer(4),
                Div,
                Integer(6)
            ]),
            Ok(2)
        }

        // 1 + 3 * 5 + 8
        assert_eq! {
            parse(iter![
                Integer(1),
                Add,
                Integer(3),
                Mul,
                Integer(5),
                Add,
                Integer(8)
            ]),
            Ok(24)
        }

        // 1 + 3 * 5 + 8 == 24
        assert_eq! {
            parse(iter![
                Integer(1),
                Add,
                Integer(3),
                Mul,
                Integer(5),
                Add,
                Integer(8),
                Eq,
                Integer(24)
            ]),
            Ok(1)
        }

        // TODO: 5 - f(3 + 2) where f = |x| x
    }

    // TODO non copy/clone test
}
