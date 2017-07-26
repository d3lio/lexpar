/// Macro that generates a parser from a formal grammar.
///
/// **NOTE:** For more info look at the tests.
/// This macro will receive a much more detailed documentation when finished.
///
/// The macro does not yet account for:
///
/// * Left Factoring
/// * Left Recursion
/// * Operator precedence
///
/// Constraints:
///
/// * The term type must be `Clone` or you'll into some issues with references.
/// * The nonterm type must derive `PartialEq, Eq, Hash`.
///
/// Crude example syntax:
///
/// ```ignore
///
/// #[derive(Debug, Clone, PartialEq)]
/// enum Token {
///     LParen,
///     RParen,
///     Number(u32),
///     Ident(String)
/// }
///
/// #[derive(Debug, PartialEq, Eq, Hash)]
/// enum Nt { E, I, P, H }
///
/// parse_rules! {
///     term: Token;
///     E => {
///         [LParen, ex:E, RParen] => {},
///         [id:I] => {},
///         [Number(n)] => {}
///     },
///     I => {
///         [Ident(name)] => {}
///     },
///     P => {
///         [@] => { /* Epsilon */ }
///     },
///     H => |rules, iter| { /* Custom code */ }
/// }
/// ```
#[macro_export]
macro_rules! parse_rules {
    {
        term: $term_type: ty;
        $($nonterm_def: tt)+
    } => {
        {
            use parser::{Parser, ParseError};

            let mut parser = Parser::new();

            parse_rules!(@NONTERM $term_type; parser; $($nonterm_def)+);

            parser
        };
    };

    // Gen code for each nonterm
    {
        @NONTERM
        $term_type: ty;
        $parser: ident;
        $nonterm: expr => {
            $(
                [$($rule_token: tt)*] => $logic: expr
            ),+
        },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $term_type; $parser; $nonterm => {
            $(
                [$($rule_token)*] => $logic
            ),+
        });

        parse_rules!(@NONTERM $term_type; $parser; $($nonterm_def)+);
    };

    // Gen code for a single nonterm
    {
        @NONTERM
        $term_type: ty;
        $parser: ident;
        $nonterm: expr => {
            $(
                [$($rule_token: tt)*] => $logic: expr
            ),+
        }
    } => {
        $parser.rule($nonterm, #[allow(unused_variables)] |rules, iter| {
            $(parse_rules! {
                @ROOT_RULE
                $term_type;
                rules; iter;
                $($rule_token)* => $logic
            })*

            // Safe to unwrap since the nonterm is guaranteeded to have at least one rule
            // and any rule before this would have returned eof err.
            #[allow(unreachable_code)]
            Err(ParseError::Unexpected(iter.next().unwrap()))
        });
    };

    // Gen code for each nonterm handle
    {
        @NONTERM
        $term_type: ty;
        $parser: ident;
        $nonterm: expr => |$rules_name: ident, $ident_name: ident| $logic: expr,
        $($nonterm_def: tt)+
    } => {
        parse_rules!{
            @NONTERM
            $term_type;
            $parser;
            $nonterm => |$rules_name, $ident_name| $logic
        }

        parse_rules!(@NONTERM $term_type; $parser; $($nonterm_def)+);
    };

    // Gen code for a single nonterm handle
    {
        @NONTERM
        $term_type: ty;
        $parser: ident;
        $nonterm: expr => |$rules_name: ident, $ident_name: ident| $logic: expr
    } => {
        $parser.rule($nonterm, #[allow(unused_variables)] |$rules_name, $ident_name| $logic);
    };

    // Epsilon
    {
        @ROOT_RULE
        $term_type: ty;
        $rules: ident;
        $iter: ident;
        @ => $logic: expr
    } => {
        return Ok($logic);
    };

    // Gen code for the first rule which is followed by more rules
    {
        @ROOT_RULE
        $term_type: ty;
        $rules: ident;
        $iter: ident;
        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                return parse_rules!(@RULE $term_type; $rules; $iter; $($rule_token)+);
            },
            Some(_) => {},
            None => return Err(ParseError::Eof)
        }
    };

    // Gen code for a singe root rule
    {
        @ROOT_RULE
        $term_type: ty;
        $rules: ident;
        $iter: ident;
        $term: pat => $logic: expr
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                return Ok($logic);
            },
            Some(_) => {},
            None => return Err(ParseError::Eof)
        }
    };

    // Gen code for each consecutive rule which is followed by more rules
    {
        @RULE
        $term_type: ty;
        $rules: ident;
        $iter: ident;
        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                parse_rules!(@RULE $term_type; $rules; $iter; $($rule_token)+)
            },
            Some(u) => Err(ParseError::Unexpected(u)),
            None => Err(ParseError::Eof)
        }
    };

    // Gen code for the last rule
    {
        @RULE
        $term_type: ty;
        $rules: ident;
        $iter: ident;
        $term: pat => $logic: expr
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                Ok($logic)
            },
            Some(u) => Err(ParseError::Unexpected(u)),
            None => Err(ParseError::Eof)
        }
    };

    // Gen code for each consecutive nonterm rule which is followed by more rules
    {
        @RULE
        $term_type: ty;
        $rules: ident;
        $iter: ident;
        $id: ident : $nonterm: expr, $($rule_token: tt)+
    } => {
        {
            let $id = ($rules.get(&$nonterm).unwrap().0)($rules, $iter);

            parse_rules!(@RULE $term_type; $rules; $iter; $($rule_token)+)
        }
    };

    // Gen code for the last nonterm rule
    {
        @RULE
        $term_type: ty;
        $rules: ident;
        $iter: ident;
        $id: ident : $nonterm: expr => $logic: expr
    } => {
        {
            let $id = ($rules.get(&$nonterm).unwrap().0)($rules, $iter);

            Ok($logic)
        }
    };
}

#[cfg(test)]
mod tests {
    use lexer::Span;
    use parser::ParseError;

    #[derive(Debug, Clone, PartialEq)]
    enum Kw {
        Fn
    }

    #[derive(Debug, Clone, PartialEq)]
    enum Token {
        Ident(String),
        Integer(u32),
        Keyword(Kw),
        Arrow
    }

    use self::Token::*;

    #[derive(Debug, PartialEq, Eq, Hash)]
    enum Nt { E, I, P }

    #[test]
    fn parser1() {
        let mut p = parse_rules! {
            term: (Span, Token);

            Nt::E => {
                [(_, Ident(name)), (_, Ident(a))] => {
                    name + &a
                }
            }
        };

        assert_eq!(p.gen(vec![
            (Span::new(1, 2, 3), Ident("hi".to_owned())),
            (Span::new(1, 2, 3), Ident("world".to_owned()))
        ].into_iter(), &Nt::E),
        Ok(String::from("hiworld")));

        assert_eq!(p.gen(vec![
            (Span::new(1, 2, 3), Ident("hi".to_owned()))
        ].into_iter(), &Nt::E),
        Err(ParseError::Eof));

        assert_eq!(p.gen(vec![
            (Span::new(1, 2, 3), Ident("hi".to_owned())), (Span::new(1, 2, 3), Integer(123))
        ].into_iter(), &Nt::E),
        Err(ParseError::Unexpected((Span::new(1, 2, 3), Integer(123)))));
    }

    #[test]
    fn parser2() {
        let mut p = parse_rules! {
            term: Token;

            Nt::E => {
                [Ident(name), Ident(a), res: Nt::I, Integer(123)] => {
                    res? + name.as_str() + a.as_str() + "E"
                }
            },
            Nt::I => {
                [Ident(name), Ident(a)] => {
                    name + a.as_str() + "I"
                }
            }
        };

        assert_eq!(p.gen(vec![
            Ident("hi".to_owned()),
            Ident("world".to_owned()),
            Ident("a".to_owned()),
            Ident("b".to_owned()),
            Integer(123)
        ].into_iter(), &Nt::E),
        Ok(String::from("abIhiworldE")));
    }

    #[test]
    fn parser3() {
        let mut p = parse_rules! {
            term: Token;

            Nt::E => {
                [Ident(name), Ident(a), res: Nt::I, Integer(123)] => {
                    res? + name.as_str() + a.as_str() + "E"
                },
                [Integer(_)] => {
                    String::from("arm 2")
                }
            },
            Nt::I => {
                [Ident(name), Ident(_), p: Nt::P] => {
                    name + "I"
                }
            },
            Nt::P => {
                [@] => {
                    String::from("eps")
                }
            }
        };

        assert_eq!(p.gen(vec![
            Ident("hi".to_owned()),
            Ident("world".to_owned()),
            Ident("a".to_owned()),
            Ident("b".to_owned()),
            Integer(123)
        ].into_iter(), &Nt::E),
        Ok(String::from("aIhiworldE")));

        assert_eq!(p.gen(vec![
            Integer(123)
        ].into_iter(), &Nt::E),
        Ok(String::from("arm 2")));
    }

    #[test]
    fn parser4() {
        let mut p = parse_rules! {
            term: Token;

            Nt::E => {
                [Keyword(Kw::Fn), Ident(name), params: Nt::I, Arrow] => {
                    let mut idents: Vec<String> = params?;
                    idents.insert(0, name);
                    idents
                }
            },
            Nt::I => |rules, iter| {
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
            }
        };

        assert_eq!(p.gen(vec![
            Keyword(Kw::Fn),
            Ident("f".to_owned()),
            Ident("a".to_owned()),
            Ident("b".to_owned()),
            Ident("c".to_owned()),
            Arrow
        ].into_iter(), &Nt::E),
        Ok(vec![
            String::from("f"),
            String::from("a"),
            String::from("b"),
            String::from("c")
        ]));
    }
}
