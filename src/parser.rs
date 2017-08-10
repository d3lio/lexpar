#[derive(Debug, Clone, PartialEq)]
pub enum ParseError<T> {
    UnexpectedRoot(T),
    Unexpected(T),
    Eof
}

pub type Result<T> = ::std::result::Result<T, ParseError<T>>;

/// Macro that generates a parser from a formal grammar.
///
/// **NOTE:** For more info look at the tests.
/// This macro will receive a much more detailed documentation in the future.
///
/// The macro does not yet account for:
///
/// * Left Factoring
/// * Left Recursion
/// * Operator precedence
///
/// ### Constraints
///
/// * The term type must be `Clone` for now.
/// * To use a nonterm as a rule it should be defined before the current nonterm.
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
/// use Token::*;
///
/// parse_rules! {
///     term: Token;
///     I => {
///         [Ident(name)] => {}
///     },
///     E => {
///         [LParen, ex:E, RParen] => {},
///         [id:I] => {},
///         [Number(n)] => {}
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
        parse_rules! {
            @NONTERM
            iter;
            ::std::iter::Peekable<Box<Iterator<Item = $term_type>>>;
            $term_type;
            $($nonterm_def)+
        }
    };

    // Loop nonterms.
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;
        $nonterm: ident => { $( [$($rule_token: tt)*] => $logic: expr ),+  $(,)* },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $nonterm => {
            $( [$($rule_token)*] => $logic ),+
        });

        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $($nonterm_def)+);
    };

    // Nonterm rules.
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;
        $nonterm: ident => { $( [$($rule_token: tt)*] => $logic: expr ),+  $(,)* } $(,)*
    } => {
        #[allow(non_snake_case, unused_variables)]
        let $nonterm = |$iter: &mut $iter_type| {
            $(parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);)*

            // Safe to unwrap since the nonterm is guaranteeded to have at least one rule
            // and any rule before this would have returned eof err.
            #[allow(unreachable_code)]
            Err(ParseError::UnexpectedRoot($iter.peek()
                .map(|peek: &$term_type| peek.clone()).unwrap()))
        };
    };

    // Loop nonterm handlers.
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;
        $nonterm: ident => |$iter_name: ident| $logic: expr,
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $nonterm => |$iter_name| $logic);
        parse_rules!(@NONTERM $iter; $iter_type; $term_type; $($nonterm_def)+);
    };

    // Nonterm handler.
    {
        @NONTERM $iter: ident; $iter_type: ty; $term_type: ty;
        $nonterm: ident => |$iter_name: ident| $logic: expr $(,)*
    } => {
        // Warn about `unused_variables` since this is your own custom code so it should
        // use the iter by either advancing it or passing it to another nonterm.
        #[allow(non_snake_case)]
        let $nonterm = |$iter_name: &mut $iter_type| $logic;
    };

    // Epsilon
    {
        @ROOT_RULE $iter: ident; $term_type: ty;
        @ => $logic: expr
    } => {
        return Ok($logic);
    };

    // First rule and more rules.
    {
        @ROOT_RULE $iter: ident; $term_type: ty;
        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.peek().map(|peek: &$term_type| peek.clone()) {
            Some($term) => {
                $iter.next();
                return parse_rules!(@RULE $iter; $($rule_token)+);
            },
            Some(_) => {},
            None => return Err(ParseError::Eof)
        }
    };

    // Only rule.
    {
        @ROOT_RULE $iter: ident; $term_type: ty;
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

    // First nonterm and more rules.
    {
        @ROOT_RULE $iter: ident; $term_type: ty;
        $id: ident : $nonterm: expr, $($rule_token: tt)+
    } => {
        // New block to prevent result sharing between branches.
        {
            #[allow(unused_variables)]
            let $id = ($nonterm)($iter);

            if let Err(ParseError::UnexpectedRoot(_)) = $id {
            } else {
                return parse_rules!(@RULE $iter; $($rule_token)+);
            }
        }
    };

    // Only nonterm.
    {
        @ROOT_RULE $iter: ident; $term_type: ty;
        $id: ident : $nonterm: expr => $logic: expr
    } => {
        // New block to prevent result sharing between branches.
        {
            #[allow(unused_variables)]
            let $id = ($nonterm)($iter);

            if let Err(ParseError::UnexpectedRoot(_)) = $id {
            } else {
                return Ok($logic);
            }
        }
    };

    // One and more rules.
    {
        @RULE $iter: ident;
        $term: pat, $($rule_token: tt)+
    } => {
        match $iter.next() {
            Some($term) => {
                parse_rules!(@RULE $iter; $($rule_token)+)
            },
            Some(u) => Err(ParseError::Unexpected(u)),
            None => Err(ParseError::Eof)
        }
    };

    // Last rule.
    {
        @RULE $iter: ident;
        $term: pat => $logic: expr
    } => {
        match $iter.next() {
            Some($term) => Ok($logic),
            Some(u) => Err(ParseError::Unexpected(u)),
            None => Err(ParseError::Eof)
        }
    };

    // Nonterm and more rules.
    {
        @RULE $iter: ident;
        $id: ident : $nonterm: expr, $($rule_token: tt)+
    } => {
        {
            #[allow(unused_variables)]
            let $id = ($nonterm)($iter);

            parse_rules!(@RULE $iter; $($rule_token)+)
        }
    };

    // Last nonterm.
    {
        @RULE $iter: ident;
        $id: ident : $nonterm: expr => $logic: expr
    } => {
        {
            #[allow(unused_variables)]
            let $id = ($nonterm)($iter);

            Ok($logic)
        }
    };
}
