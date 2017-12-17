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
            @NONTERM __iter; $term_type;
            $($nonterm_def)+
        }
    };

    // Loop nonterms
    //
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
    //
    // <nonterm>: <type> => |<iter>| { ... }
    {
        @NONTERM $iter: ident; $term_type: ty;

        $nonterm: ident : $ret_type: ty => |$iter_name: ident| $logic: expr,
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $term_type; $nonterm : $ret_type => |$iter_name| $logic);

        parse_rules!(@NONTERM $iter; $term_type; $($nonterm_def)+);
    };

    // Loop folds
    //
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

    // Loop bin ops
    //
    // #[binop(<affix>)] <nonterm>: <type> => { ... }
    {
        @NONTERM $iter: ident; $term_type: ty;

        #[binop($affix: ident)]
        $nonterm: ident : $ret_type: ty => $primary: ident : $prim_type: ty where
        $__prec_name: ident : $prec_type:ty => |$lhs: ident, $rhs: ident| {
            $($binop_def: tt)+
        },
        $($nonterm_def: tt)+
    } => {
        parse_rules!(@NONTERM $iter; $term_type; #[binop($affix)]
        $nonterm: $ret_type => $primary: $prim_type where $__prec_name: $prec_type => |$lhs, $rhs| {
            $($binop_def)+
        });

        parse_rules!(@NONTERM $iter; $term_type; $($nonterm_def)+);
    };

    // Nonterm rules
    //
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
    //
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
    //
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
        parse_rules!(@NONTERM $iter; $term_type; $nonterm: $ret_type => |$iter| {
            use ::lexpar::parser::{self, UnshiftIter};

            type ParserResult = parser::Result<$ret_type, $term_type>;

            fn matcher_root<I>($iter: &mut UnshiftIter<I>, $acc: $ret_type) -> ParserResult
            where I: Iterator<Item = $term_type>
            {
                #[allow(unused_mut)]
                let mut $acc = $acc;

                parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);

                #[allow(unreachable_code)]
                Ok($acc)
            }

            fn matcher<I>($iter: &mut UnshiftIter<I>, $acc: $ret_type, __ur: &mut bool) -> ParserResult
            where I: Iterator<Item = $term_type>
            {
                #[allow(unused_mut)]
                let mut $acc = $acc;

                parse_rules!(@ROOT_RULE $iter; $term_type; $($rule_token)* => $logic);

                if $iter.peek().is_some() {
                    *__ur = true;
                }

                #[allow(unreachable_code)]
                Ok($acc)
            }

            let mut acc = $acc_expr;
            let mut unexpected_root = false;

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
                    (matcher)($iter, acc, &mut unexpected_root) =>
                    $iter.peek().is_none() || unexpected_root
                }
            }
        });
    };

    // Infix binop syntax
    //
    // #[binop(infix)] <nonterm>: <type> => <primary_nonterm>: <primary_type>
    // where precedence: <prec_type> => |<lhs>, <rhs>| {
    //     (<op> | <precedence> => logic),+
    // }
    {
        @NONTERM $iter: ident; $term_type: ty;

        #[binop($affix: ident)]
        $nonterm: ident : $ret_type: ty => $primary: ident : $prim_type: ty where
        $__prec_name: ident : $prec_type:ty => |$lhs: ident, $rhs: ident| {
                $($op: pat | $precedence: expr => $logic: expr),+
                $(,)*
            }
            $(,)*
    } => {
        /*
        parse_expression ()
            return parse_binop (parse_primary (), 0)

        parse_binop (lhs, min_precedence)
            lookahead := peek next token
            while lookahead is a binary operator whose precedence is >= min_precedence
                op := lookahead
                advance to next token
                rhs := parse_primary ()
                lookahead := peek next token
                while lookahead is a binary operator whose precedence is greater
                        than op's, or a right-associative operator
                        whose precedence is equal to op's
                    rhs := parse_binop (rhs, lookahead's precedence)
                    lookahead := peek next token
                lhs := the result of applying op with operands lhs and rhs
            return lhs
        */

        parse_rules!(@NONTERM $iter; $term_type; $nonterm: $ret_type => |$iter| {
            use ::lexpar::parser::{self, UnshiftIter};
            use ::lexpar::parser::ParseError::*;

            type ParserResult = parser::Result<$ret_type, $term_type>;

            fn prec(term: &$term_type) -> Option<$prec_type> {
                #[allow(unused_variables)]
                match term {
                    $($op => Some($precedence)),+,
                    _ => None
                }
            }

            fn eval(__term: &$term_type, $lhs: $prim_type, $rhs: $prim_type) -> $ret_type {
                match __term {
                    $($op => $logic),+,
                    _ => unreachable!()
                }
            }

            fn parse_binop<I>($iter: &mut UnshiftIter<I>, mut lhs: $prim_type, min_prec: $prec_type)
                -> ParserResult where I: Iterator<Item = $term_type>
            {
                while let Some(la) = $iter.next() {
                    match prec(&la) {
                        Some(precedence) if precedence >= min_prec => {
                            let op = la;
                            let mut rhs = match $primary($iter) {
                                Ok(rhs) => rhs,
                                Err(Eof) | Err(UnexpectedRoot) => break,
                                Err(err) => return Err(err)
                            };

                            while let Some(la_inner) = $iter.next() {
                                match prec(&la_inner) {
                                    Some(next_prec) if next_prec > precedence => {
                                        $iter.unshift(la_inner);
                                        rhs = match parse_binop($iter, rhs, next_prec) {
                                            Ok(rhs) => rhs,
                                            Err(err) => return Err(err)
                                        };
                                    },
                                    _ => {
                                        $iter.unshift(la_inner);
                                        break;
                                    }
                                }
                            }

                            lhs = eval(&op, lhs, rhs);
                        },
                        _ => {
                            $iter.unshift(la);
                            break;
                        }
                    }
                }

                Ok(lhs)
            }

            // with the + repetition it's guaranteed that there will be at least one element
            let min_prec = vec![ $($precedence),+ ].into_iter().min().unwrap();

            let lhs = $primary($iter)?;
            parse_binop($iter, lhs, min_prec)
        });
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
