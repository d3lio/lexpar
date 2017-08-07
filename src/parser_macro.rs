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
/// * The term type must be `Clone` or you'll run into some issues with references.
/// * The nonterm type must derive `PartialEq, Eq, Hash`.
///
/// ### Crude example syntax
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
/// use Token::*;
/// use Nt::*;
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
    // Full definition.
    // Unexpected and Eof are closures to prevent unexpected behaviour when using return.
    {
        parser: $parser: ident;
        term: $term_type: ty;
        unexpected: $unexpected: expr;
        eof: $eof: expr;
        $($nonterm_def: tt)+
    } => {
        {
            parse_rules! {
                @NONTERM
                $parser;
                $term_type;
                $unexpected;
                $eof;
                $($nonterm_def)+
            }
        }
    };

    // Use an existing parser to extend it's rules.
    // Useful when the macro recursion limit is reached.
    {
        parser: $parser: ident;
        term: $term_type: ty;
        $($nonterm_def: tt)+
    } => {
        {
            use parser::ParseError;
            parse_rules! {
                parser: $parser;
                term: $term_type;
                unexpected: |term| Err(ParseError::Unexpected(term));
                eof: || Err(ParseError::Eof);
                $($nonterm_def)+
            }
        }
    };

    // Creates the parser for you.
    {
        term: $term_type: ty;
        $($nonterm_def: tt)+
    } => {
        {
            let mut parser = ::parser::Parser::new();

            parse_rules! {
                parser: parser;
                term: $term_type;
                $($nonterm_def)+
            }

            parser
        }
    };

    // Gen code for each nonterm.
    {
        @NONTERM
        $parser: ident;
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $nonterm: expr => {
            $(
                [$($rule_token: tt)*] => $logic: expr
            ),+
        },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $parser; $term_type; $unexpected; $eof; $nonterm => {
            $(
                [$($rule_token)*] => $logic
            ),+
        });

        parse_rules!(@NONTERM $parser; $term_type; $unexpected; $eof; $($nonterm_def)+);
    };

    // Gen code for a single nonterm.
    {
        @NONTERM
        $parser: ident;
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
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
                $unexpected;
                $eof;
                rules;
                iter;
                $($rule_token)* => $logic
            })*

            // Safe to unwrap since the nonterm is guaranteeded to have at least one rule
            // and any rule before this would have returned eof err.
            #[allow(unreachable_code)]
            ($unexpected)(iter.next().unwrap())
        });
    };

    // Gen code for each nonterm handle.
    {
        @NONTERM
        $parser: ident;
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $nonterm: expr => |$rules_name: ident, $ident_name: ident| $logic: expr,
        $($nonterm_def: tt)+
    } => {
        parse_rules!{
            @NONTERM
            $parser;
            $term_type;
            $unexpected;
            $eof;
            $nonterm => |$rules_name, $ident_name| $logic
        }

        parse_rules!(@NONTERM $parser; $term_type; $unexpected; $eof; $($nonterm_def)+);
    };

    // Gen code for a single nonterm handle.
    {
        @NONTERM
        $parser: ident;
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $nonterm: expr => |$rules_name: ident, $ident_name: ident| $logic: expr
    } => {
        $parser.rule($nonterm, #[allow(unused_variables)] |$rules_name, $ident_name| $logic);
    };

    // Epsilon
    {
        @ROOT_RULE
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $rules: ident;
        $iter: ident;
        @ => $logic: expr
    } => {
        return Ok($logic);
    };

    // Gen code for the first rule which is followed by more rules.
    {
        @ROOT_RULE
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $rules: ident;
        $iter: ident;
        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                return parse_rules! {
                    @RULE
                    $term_type;
                    $unexpected;
                    $eof;
                    $rules;
                    $iter;
                    $($rule_token)+
                }
            },
            Some(_) => {},
            None => return ($eof)()
        }
    };

    // Gen code for a singe root rule.
    {
        @ROOT_RULE
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
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
            None => return ($eof)()
        }
    };

    // Gen code for each consecutive rule which is followed by more rules.
    {
        @RULE
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $rules: ident;
        $iter: ident;
        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                parse_rules! {
                    @RULE
                    $term_type;
                    $unexpected;
                    $eof;
                    $rules;
                    $iter;
                    $($rule_token)+
                }
            },
            Some(u) => ($unexpected)(u),
            None => ($eof)()
        }
    };

    // Gen code for the last rule.
    {
        @RULE
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $rules: ident;
        $iter: ident;
        $term: pat => $logic: expr
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                Ok($logic)
            },
            Some(u) => ($unexpected)(u),
            None => ($eof)()
        }
    };

    // Gen code for each consecutive nonterm rule which is followed by more rules.
    {
        @RULE
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
        $rules: ident;
        $iter: ident;
        $id: ident : $nonterm: expr, $($rule_token: tt)+
    } => {
        {
            let $id = ($rules.get(&$nonterm).unwrap().0)($rules, $iter);

            parse_rules! {
                @RULE
                $term_type;
                $unexpected;
                $eof;
                $rules;
                $iter;
                $($rule_token)+
            }
        }
    };

    // Gen code for the last nonterm rule.
    {
        @RULE
        $term_type: ty;
        $unexpected: expr;
        $eof: expr;
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
    fn parser1_ok_eof_unexpected() {
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
    fn parser2_nonterm() {
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
    fn parser3_epsilon() {
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
    fn parser4_custom_handler() {
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

    #[test]
    fn parser5_custom_eof_unexpected() {
        let mut p = ::parser::Parser::new();

        parse_rules! {
            parser: p;
            term: (Span, Token);
            unexpected: |_| Err(0);
            eof: || Err(1);

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
        Err(1));

        assert_eq!(p.gen(vec![
            (Span::new(1, 2, 3), Ident("hi".to_owned())), (Span::new(1, 2, 3), Integer(123))
        ].into_iter(), &Nt::E),
        Err(0));
    }
}
