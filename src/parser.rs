use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError<T> {
    Unexpected(T),
    Eof,
    #[doc(hidden)]
    UnexpectedRoot
}

pub type Result<P, T> = ::std::result::Result<P, ParseError<T>>;

/// Unshiftable interator
///
/// Can unshift one element back into the iterator as the next element to be iterated.
pub struct UnshiftIter<I> where I: Iterator {
    iter: Peekable<I>,
    head: Option<I::Item>
}

impl<I> From<I> for UnshiftIter<I> where I: Iterator {
    fn from(iter: I) -> Self {
        Self {
            iter: iter.peekable(),
            head: None
        }
    }
}

impl<I> Iterator for UnshiftIter<I> where I: Iterator {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.head.is_some() {
            self.head.take()
        } else {
            self.iter.next()
        }
    }
}

impl<I> UnshiftIter<I> where I: Iterator {
    pub fn unshift(&mut self, item: I::Item) {
        self.head = Some(item);
    }

    pub fn peek(&mut self) -> Option<&I::Item> {
        match self.head {
            Some(ref item) => Some(item),
            None => self.iter.peek()
        }
    }
}

/// Helper macro for folding
///
/// Covers a common case when folding matches into a vector
///
/// # Example
///
/// ```ignore
/// #[fold(exprs)]
/// top_level: Vec<AstNode> => {
///     [ex: expr] => {
///         let mut exprs = exprs;
///         exprs.push(ex?);
///         exprs
///     },
///     [@] => Vec::new()
/// }
/// ```
///
/// becomes
///
/// ```ignore
/// #[fold(exprs)]
/// top_level: Vec<AstNode> => {
///     [ex: expr] => fold_vec!(exprs, ex?),
///     [@] => Vec::new()
/// }
/// ```
#[macro_export]
macro_rules! fold_vec {
    ($acc: ident, $ex: expr) => {{
        let mut v = $acc;
        v.push($ex);
        v
    }}
}

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
/// ### Crude example syntax
///
/// ```no_run
/// # #[macro_use]
/// # extern crate lexpar;
///
/// #[derive(Debug, PartialEq)]
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
            // `iter` is necessery to be passed so that each arm has iter in its macro scope
            @NONTERM iter; $term_type;
            $($nonterm_def)+
        }
    };

    // Loop nonterms
    // <nonterm>: <type> => { ... }
    {
        @NONTERM $iter: ident; $term_type: ty;

        $nonterm: ident : $ret_type: ty => {
            $( [$($rule_token: tt)*] => $logic: expr ),+
            $(,)*
        },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $term_type; $nonterm : $ret_type => {
            $( [$($rule_token)*] => $logic ),+
        });

        parse_rules!(@NONTERM $iter; $term_type; $($nonterm_def)+);
    };

    // Loop nonterm handlers
    // <nonterm>: <type> => |<iter>| { ... }
    {
        @NONTERM $iter: ident; $term_type: ty;

        $nonterm: ident : $ret_type: ty => |$iter_name: ident| $logic: expr,
        $($nonterm_def: tt)+
    } => {
        parse_rules! {
            @NONTERM $iter; $term_type; $nonterm : $ret_type => |$iter_name| $logic
        }

        parse_rules!(@NONTERM $iter; $term_type; $($nonterm_def)+);
    };

    // Loop folds
    // #[fold(<acc>)] <nonterm>: <type> => { ... }
    {
        @NONTERM $iter: ident; $term_type: ty;

        #[fold($acc: ident)]
        $nonterm: ident : $ret_type: ty => {
            [$($rule_token: tt)*] => $logic: expr,
            [@] => $acc_expr: expr
            $(,)*
        },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $term_type; #[fold($acc)] $nonterm : $ret_type => {
            [$($rule_token)*] => $logic,
            [@] => $acc_expr
        });

        parse_rules!(@NONTERM $iter; $term_type; $($nonterm_def)+);
    };

    // Nonterm rules
    // <nonterm>: <type> => { arms+ }
    {
        @NONTERM $iter: ident; $term_type: ty;

        $nonterm: ident : $ret_type: ty => {
            $( [$($rule_token: tt)*] => $logic: expr ),+
            $(,)*
        } $(,)*
    } => {
        // Disable the warning since Epsilon does not use iter
        #[allow(unused_variables)]
        fn $nonterm<I>($iter: &mut ::lexpar::parser::UnshiftIter<I>)
            -> ::lexpar::parser::Result<$ret_type, $term_type>
        where I: Iterator<Item = $term_type>
        {
            $(parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);)*

            #[allow(unreachable_code)]
            match $iter.peek() {
                Some(_) => Err(::lexpar::parser::ParseError::UnexpectedRoot),
                None => Err(::lexpar::parser::ParseError::Eof)
            }
        }
    };

    // Nonterm handler
    // |iter| => expr
    {
        @NONTERM $iter: ident; $term_type: ty;

        $nonterm: ident : $ret_type: ty => |$iter_name: ident| $logic: expr $(,)*
    } => {
        fn $nonterm<I>($iter_name: &mut ::lexpar::parser::UnshiftIter<I>)
            -> ::lexpar::parser::Result<$ret_type, $term_type>
        where I: Iterator<Item = $term_type>
        {
            $logic
        }
    };

    // Fold syntax
    // #[fold(<acc>)] <nonterm>: <type> => {
    //     [ rules+ ] => logic,
    //     [@] => start_acc
    // }
    {
        @NONTERM $iter: ident; $term_type: ty;

        #[fold($acc: ident)]
        $nonterm: ident : $ret_type: ty => {
            [$($rule_token: tt)*] => $logic: expr,
            [@] => $acc_expr: expr
            $(,)*
        } $(,)*
    } => {
        #[allow(unused_variables)]
        fn $nonterm<I>($iter: &mut ::lexpar::parser::UnshiftIter<I>)
            -> ::lexpar::parser::Result<$ret_type, $term_type>
        where I: Iterator<Item = $term_type>
        {
            use ::lexpar::parser;

            let mut acc = $acc_expr;
            let mut unexpected_root = false;

            fn matcher_root<I>($iter: &mut ::lexpar::parser::UnshiftIter<I>,
                            $acc: $ret_type) -> parser::Result<$ret_type, $term_type>
            where I: Iterator<Item = $term_type>
            {
                parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);

                #[allow(unreachable_code)]
                match $iter.peek() {
                    Some(_) => Err(parser::ParseError::UnexpectedRoot),
                    None => Ok($acc)
                }
            };

            // $acc should not be named `$iter` or `unexpected_root`
            fn matcher<I>($iter: &mut ::lexpar::parser::UnshiftIter<I>,
                       unexpected_root: &mut bool,
                       $acc: $ret_type) -> parser::Result<$ret_type, $term_type>
            where I: Iterator<Item = $term_type>
            {
                parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);

                if $iter.peek().is_some() {
                    *unexpected_root = true;
                }

                #[allow(unreachable_code)]
                Ok($acc)
            };

            macro_rules! matcher {
                ($matcher: expr => $end_cond: expr) => {
                    match $matcher {
                        Ok(res) => {
                            if $end_cond {
                                return Ok(res);
                            } else {
                                acc = res;
                            }
                        },
                        Err(err) => return Err(err)
                    }
                };
            }

            matcher!((matcher_root)($iter, acc) => $iter.peek().is_none());

            loop {
                matcher!{
                    (matcher)($iter, &mut unexpected_root, acc) =>
                    $iter.peek().is_none() || unexpected_root
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
        let item = $iter.next();

        match item {
            Some($term) => {
                return parse_rules!(@RULE $iter; $($rule_token)+);
            },
            // Skip to the next branch of the nonterm
            Some(_) => {
                $iter.unshift(item.unwrap());
            },
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
        let item = $iter.next();

        match item {
            Some($term) => {
                return Ok($logic);
            },
            // Skip to the next branch of the nonterm
            Some(_) => {
                $iter.unshift(item.unwrap());
            },
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
        let $id = $nonterm($iter);

        if let Err(::lexpar::parser::ParseError::UnexpectedRoot) = $id {
            // Skip to the next branch of the nonterm
        } else {
            return parse_rules!(@RULE $iter; $($rule_token)+);
        }
    };

    // Only nonterm
    {
        @ROOT_RULE $iter: ident; $term_type: ty;

        $id: ident : $nonterm: expr => $logic: expr
    } => {
        let $id = $nonterm($iter);

        if let Err(::lexpar::parser::ParseError::UnexpectedRoot) = $id {
            // Skip to the next branch of the nonterm
        } else {
            return Ok($logic);
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
