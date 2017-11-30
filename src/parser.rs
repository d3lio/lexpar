#[derive(Debug, Clone, PartialEq)]
pub enum ParseError<T> {
    UnexpectedRoot(T),
    Unexpected(T),
    Eof
}

pub type Result<P, T> = ::std::result::Result<P, ParseError<T>>;

/// Macro that generates a parser from a formal grammar.
///
/// **NOTE:** For more info look at the tests.
/// This macro will receive a much more detailed documentation in the future.
///
/// The macro does not yet account for:
///
/// * Left Factoring (`A -> qB | qC`)
/// * Left Recursion (`A -> Aq` (direct) or `A -> Bq B -> Ar` (indirect))
/// * Operator precedence (A + B * C)
///
/// ### Constraints
///
/// * The term type must be `Clone` for now.
///
/// ### Crude example syntax
///
/// ```no_run
/// # #[macro_use]
/// # extern crate lexpar;
///
/// #[derive(Debug, Clone, PartialEq)]
/// enum Token {
///     LParen,
///     RParen,
///     Number(u32),
///     Ident(String)
/// }
///
/// # fn main() {
/// use Token::*;
///
/// parse_rules! {
///     term: Token;
///     ident: () => {
///         [Ident(name)] => {}
///     },
///     expr: () => {
///         [LParen, ex: expr, RParen] => {},
///         [id: ident] => {},
///         [Number(n)] => {}
///     },
///     eps: () => {
///         [@] => { /* Epsilon */ }
///     },
///     handle: () => |iter| Ok({ /* Custom code */ })
/// }
/// # }
/// ```
#[macro_export]
macro_rules! parse_rules {
    {
        term: $term_type: ty;
        $($nonterm_def: tt)+
    } => {
        parse_rules! {
            @NONTERM iter; ::std::iter::Peekable<Box<Iterator<Item = $term_type>>>; $term_type;
            $($nonterm_def)+
        }
    };

    // Loop nonterms
    // <nonterm>: <type> => { ... }
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;

        $nonterm: ident : $ret_type: ty => {
            $( [$($rule_token: tt)*] => $logic: expr ),+
            $(,)*
        },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $nonterm : $ret_type => {
            $( [$($rule_token)*] => $logic ),+
        });

        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $($nonterm_def)+);
    };

    // Loop nonterm handlers
    // <nonterm>: <type> => |<iter>| { ... }
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;

        $nonterm: ident : $ret_type: ty => |$iter_name: ident| $logic: expr,
        $($nonterm_def: tt)+
    } => {
        parse_rules! {
            @NONTERM $iter; $iter_type; $term_type; $nonterm : $ret_type => |$iter_name| $logic
        }

        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $($nonterm_def)+);
    };

    // Loop folds
    // fold <nonterm>: <type> as <acc> => { ... }
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;

        #[fold($acc: ident)]
        $nonterm: ident : $ret_type: ty => {
            [$($rule_token: tt)*] => $logic: expr,
            [@] => $acc_expr: expr
            $(,)*
        },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $iter_type; $term_type; #[fold($acc)] $nonterm : $ret_type => {
            [$($rule_token)*] => $logic,
            [@] => $acc_expr
        });

        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $($nonterm_def)+);
    };

    // Nonterm rules
    // <nonterm>: <type> => { (rules)+ }
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;

        $nonterm: ident : $ret_type: ty => {
            $( [$($rule_token: tt)*] => $logic: expr ),+
            $(,)*
        } $(,)*
    } => {
        // Disable the warning since Epsilon does not use iter
        #[allow(unused_variables)]
        fn $nonterm($iter: &mut $iter_type) -> ::lexpar::parser::Result<$ret_type, $term_type> {
            $(parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);)*

            #[allow(unreachable_code)]
            match $iter.peek().map(|peek: &$term_type| peek.clone()) {
                Some(u) => Err(::lexpar::parser::ParseError::UnexpectedRoot(u)),
                None => Err(::lexpar::parser::ParseError::Eof)
            }
        }
    };

    // Nonterm handler
    // |iter| => expr
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;

        $nonterm: ident : $ret_type: ty => |$iter_name: ident| $logic: expr $(,)*
    } => {
        fn $nonterm($iter_name: &mut $iter_type) -> ::lexpar::parser::Result<$ret_type, $term_type> {
            $logic
        }
    };

    // Fold syntax
    // fold <nonterm>: <type> as <acc> => {
    //     [rules+, nonterm] => logic,
    //     [@] => start_acc
    // }
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;

        #[fold($acc: ident)]
        $nonterm: ident : $ret_type: ty => {
            [$($rule_token: tt)*] => $logic: expr,
            [@] => $acc_expr: expr
            $(,)*
        } $(,)*
    } => {
        #[allow(unused_variables)]
        fn $nonterm($iter: &mut $iter_type) -> ::lexpar::parser::Result<$ret_type, $term_type> {
            use ::lexpar::parser::Result;

            let mut acc = $acc_expr;
            let mut unexpected_root = false;

            fn matcher_root($iter: &mut $iter_type, $acc: $ret_type) -> Result<$ret_type, $term_type> {
                parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);

                #[allow(unreachable_code)]
                match $iter.peek().map(|peek: &$term_type| peek.clone()) {
                    Some(u) => Err(::lexpar::parser::ParseError::UnexpectedRoot(u)),
                    None => Ok($acc)
                }
            };

            // $acc should not be named `$iter` or `unexpected_root`
            fn matcher($iter: &mut $iter_type,
                       unexpected_root: &mut bool,
                       $acc: $ret_type) -> Result<$ret_type, $term_type>
            {
                parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);

                if let Some(u) = $iter.peek().map(|peek: &$term_type| peek.clone()) {
                    *unexpected_root = true;
                }

                #[allow(unreachable_code)]
                Ok($acc)
            };

            match (matcher_root)($iter, acc) {
                Ok(res) => {
                    if $iter.peek().is_none() {
                        return Ok(res);
                    } else {
                        acc = res;
                    }
                },
                Err(err) => return Err(err)
            }

            loop {
                match (matcher)($iter, &mut unexpected_root, acc) {
                    Ok(res) => {
                        if $iter.peek().is_none() || unexpected_root {
                            break Ok(res);
                        } else {
                            acc = res;
                        }
                    },
                    Err(err) => break Err(err)
                }
            }
        }
    };

    // Epsilon
    {
        @ROOT_RULE $iter: ident; $term_type: ty;

        @ => $logic: expr
    } => {
        return Ok($logic);
    };

    // First rule and more rules
    {
        @ROOT_RULE $iter: ident; $term_type: ty;

        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                return parse_rules!(@RULE $iter; $($rule_token)+);
            },
            // Skip to the next branch of the nonterm
            Some(_) => (),
            // Let the nonterm handle the eof
            // This is so we can enter an Epsilon root rule if it exists
            None => ()
        }
    };

    // Only rule
    {
        @ROOT_RULE $iter: ident; $term_type: ty;

        $term: pat => $logic: expr
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                return Ok($logic);
            },
            // Skip to the next branch of the nonterm
            Some(_) => (),
            // Let the nonterm handle the eof
            // This is so we can enter an Epsilon root rule if it exists
            None => ()
        }
    };

    // First nonterm and more rules
    {
        @ROOT_RULE $iter: ident; $term_type: ty;

        $id: ident : $nonterm: expr, $($rule_token: tt)+
    } => {
        // New block to prevent result sharing between branches
        {
            #[allow(unused_variables)]
            let $id = $nonterm($iter);

            if let Err(::lexpar::parser::ParseError::UnexpectedRoot(_)) = $id {
                // Skip to the next branch of the nonterm
            } else {
                return parse_rules!(@RULE $iter; $($rule_token)+);
            }
        }
    };

    // Only nonterm
    {
        @ROOT_RULE $iter: ident; $term_type: ty;

        $id: ident : $nonterm: expr => $logic: expr
    } => {
        // New block to prevent result sharing between branches
        {
            #[allow(unused_variables)]
            let $id = $nonterm($iter);

            if let Err(::lexpar::parser::ParseError::UnexpectedRoot(_)) = $id {
                // Skip to the next branch of the nonterm
            } else {
                return Ok($logic);
            }
        }
    };

    // One and more rules
    {
        @RULE $iter: ident;

        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.next() {
            Some($term) => {
                parse_rules!(@RULE $iter; $($rule_token)+)
            },
            Some(u) => Err(::lexpar::parser::ParseError::Unexpected(u)),
            None => Err(::lexpar::parser::ParseError::Eof)
        }
    };

    // Last rule
    {
        @RULE $iter: ident;

        $term: pat => $logic: expr
    } => {
        match $iter.next() {
            Some($term) => Ok($logic),
            Some(u) => Err(::lexpar::parser::ParseError::Unexpected(u)),
            None => Err(::lexpar::parser::ParseError::Eof)
        }
    };

    // Nonterm and more rules
    {
        @RULE $iter: ident;

        $id: ident : $nonterm: expr, $($rule_token: tt)+
    } => {
        {
            #[allow(unused_variables)]
            let $id = $nonterm($iter);

            parse_rules!(@RULE $iter; $($rule_token)+)
        }
    };

    // Last nonterm
    {
        @RULE $iter: ident;

        $id: ident : $nonterm: expr => $logic: expr
    } => {
        {
            #[allow(unused_variables)]
            let $id = $nonterm($iter);

            Ok($logic)
        }
    };
}
