//! This module contains parser related macros and structures.
//!
//! The following chapters will walk you through the basics of the `parse_rules` macro.
//! Prior knowledge of [formal grammars](https://en.wikipedia.org/wiki/Formal_grammar)
//! is recommended but not necessary. If you are familiar with grammars just skip to the
//! basic syntax section.
//!
//! # Introduction
//!
//! First of all why do we need parsers? Well, we need a way to express grammars so that we abstract
//! away from automatas and think about grammars in a more intuitive manner. This more intuitive
//! way would be pattern matching. Let say we have this code snippet
//!
//! `x = 1 + 2 * 3`
//!
//! Depending on the context we as humans we can easily parse this in our heads:
//!
//! > Assign to a variable called "x" the expression 1 + 2 * 3
//!
//! And as we are familiar with basic maths the expression 1 + 2 * 3 would result in the number 7.
//! So we now have the following human expression
//!
//! > Assign the number 7 to a variable called "x"
//!
//! or shorter
//!
//! > Assign 7 to "x"
//!
//! So what we did here is we looked at the code and matched familiar patterns from what we have
//! seen in our experience with programming languages and maths.
//!
//! The thing is that machines can't differentiate contexts as well as humans unless they are
//! programmed to. For a machine this could mean
//!
//! > Is x equal to 9? Where 9 is (1 + 2) * 3.
//!
//! or just a bunch of numbers
//!
//! > `120 32 61 32 49 32 43 32 50 32 42 32 51`
//!
//! Directly using [Automatas](https://en.wikipedia.org/wiki/Automata_theory) could tell the machine
//! how to recognize these patterns by switching between states and so on but they are not really
//! intuitive for humans especially when the grammar we want to parse is large.
//!
//! This is where formal grammars and parsers come in.
//!
//! # Basic syntax of the parse_rules macro
//!
//! Say we have the following grammar
//!
//! > Expression -> Number<br>
//! > Expression -> ( Expression )
//!
//! This means that an expression can be a single number or another expression surrounded with
//! parenthesis. The grammar would recognize expressions like
//!
//! > `1`<br>
//! > `(123)`<br>
//! > `(((5)))`
//!
//! The `parse_rules!` macro can be used to express that in a Rusty way
//!
//! ```no_run
//! # #[macro_use]
//! # extern crate lexpar;
//! enum Token {
//!     LParen,
//!     RParen,
//!     Number(u32)
//! }
//!
//! # fn main() {
//! use Token::*;
//!
//! parse_rules! {
//!     term: Token;
//!
//!     expression: u32 => {
//!         [Number(value)] => value,
//!         [LParen, expr: expression, RParen] => expr?
//!     }
//! }
//! # }
//! ```
//!
//! Lets break this down. The first thing you might have noticed is `term: Token;`. What this does
//! is it tells the macro that the type of each item (terminal) of the input that we are going to
//! parse is `Token`.
//!
//! The `expression: u32 => { /* ... */ }` notation defines a new function called `expression`
//! with a return type `u32`. So now we have a function that looks like this
//!
//! ```no_run
//! fn expression(/* ... */) -> u32 {
//!     // ...
//! # 0
//! }
//! ```
//!
//! This function is the representation of a nonterminal for a formal grammar. When called it
//! parses the input based on whatever rules we've defined and spits out a `u32`. We'll take a look
//! at how input is passed to the function in a moment.
//!
//! For now lets see what are these array looking things inside the notation
//!
//! ```no_run
//! # #[macro_use]
//! # extern crate lexpar;
//! # enum Token { LParen, RParen, Number(u32) }
//! # fn main() {
//! # use Token::*;
//! # parse_rules! { term: Token; expression: u32 => {
//! [Number(value)] => value,
//! [LParen, expr: expression, RParen] => expr?
//! # }}}
//! ```
//!
//! Those are the rules of a nonterminal. It's very similar to Rust's `match`. Each rules is an arm
//! of the match. They are also comma seperated. There are differences. One of them is that each
//! rule follows this format
//!
//! ```ignore
//! [ (terminal|nonterminal)+ ] => rust_expression
//! ```
//!
//! Inside the brackets we can match more than just patterns (terminals), we can match
//! function calls (nonterminals). What that means is that we can invoke another function generated
//! by the macro and then decide what to do with the result. Example syntax would be
//!
//! * `Number(num)` is a destructuring pattern
//! * `expr: expression` expands to the statement `let expr = expression(/* ... */)`
//!
//! In our little example `expr: expression` is a recursive call of `expression`. As we said the
//! return value is always a `Result`. That's why we can see the `expr?` in
//!
//! ```ignore
//! [LParen, expr: expression, RParen] => expr?
//! ```
//!
//! Thats just Rust's `?` operator to propagate parsing errors.
//!
//! Extending the example into a slower and more verbose form shows how multiple nonterminals
//! can be defined
//!
//! ```no_run
//! # #[macro_use]
//! # extern crate lexpar;
//! # enum Token { LParen, RParen, Number(u32) }
//! # fn main() {
//! # use Token::*;
//! parse_rules! {
//!     term: Token;
//!
//!     number: u32 => {
//!         [Number(value)] => value
//!     },
//!
//!     expression: u32 => {
//!         [num: number] => num?,
//!         [LParen, expr: expression, RParen] => expr?
//!     }
//! }
//! # }
//! ```
//!
//! # Using the parser
//!
//! Now we have this 'parser' generated for us but how do we use it?
//! Well there is no `Parser` structure or anything. The macro generates the private nonterminal
//! functions and leaves the rest to the user.
//!
//! Each function takes an iterator but not just any iterator - `lexpar::parser::UnshiftIter`.
//! To ease the import and use of that exact iterator we can call any nonterminal like this
//!
//! ```
//! # fn expression<I>(_: ::lexpar::parser::UnshiftIter<I>) where I: Iterator {}
//! # enum Token { LParen, RParen, Number(u32) }
//! # fn main() {
//! # use Token::*;
//! let input = vec![LParen, Number(42), RParen].into_iter();
//!
//! let result = expression(input.into());
//! # }
//! ```
//!
//! After we get a result we should match it for any parsing errors
//!
//! ```
//! # enum Token { LParen, RParen, Number(u32) }
//! use lexpar::parser::{self, ParseError};
//!
//! let result: parser::Result<u32, Token> = Ok(0u32);
//!
//! match result {
//!     Ok(value) => { /* Do something with the value */ },
//!     Err(ParseError::Eof) => { /* Unexpected end of input */ },
//!     Err(ParseError::Unexpected(token)) => { /* Unexpected token */ },
//!     Err(ParseError::UnexpectedRoot) => { /* Unexpected head token */ }
//! }
//! ```
//!
//! # User defined errors
//!
//! If necessary a nonterminal can be defined with a return type as `Result<...>`. Then we can have
//! more than just the normal parsing errors - we can match each nonterminal result instead of
//! propagating it with `?` and assemble our own errors and warnings. This could be used to
//! improve syntax errors for your compiler/interpreter.
//!
//! Right now the parsers is limited in the way that we have to handle custom errors ourselves
//! instead of using the macro to do it for us. This is a future goal for improvement.
//!
//! # Epsilon, recursion and folding
//!
//! What we know until now is that we can use the macro to express `and` and `or` with match arms
//! and recursive grammars by calling the same nonterminal.
//!
//! There are some more complex compositions we might need to parse for example:
//!
//! * `?` - `zero or one`
//! * `*` - `zero or more`
//! * `+` - `one or more`
//!
//! ### Zero or one
//!
//! This sound like Rust's `Option`, doesn't it? Well it does.
//!
//! Lets see how to express that
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! enum Token {
//!     Something
//! }
//!
//! # use self::Token::*;
//! # fn main() {
//! parse_rules! {
//!     term: Token;
//!
//!     zero_or_one: Option<()> => {
//!         [Token::Something] => Some(()),
//!         [@] => None
//!     }
//! }
//! # }
//! ```
//!
//! Everything seems familiar except `[@]`. What is that?
//! Grammars have the concept of an 'empty token'. It's usually called `epsilon` and that's how
//! we'll call it as well. It is used to express that any token is a match.
//!
//! To get a better idea of epsilon imagine a string split into characters where epsilon is the
//! empty string/character. It changes nothing but can always be put in between other characters
//! without changing the final result.
//!
//! So the epsilon is a away of saying
//!
//! > Nothing matched so far but it's OK since we can use this default value.
//!
//! much like an else (`_ =>`) arm for match statements.
//!
//! It can be used only as the last arm of a nonterminal.
//!
//! ### Zero or more (Kleene star)
//!
//! Now this one is a bit trickier. I'll try not to bore you with set theory
//! so lets jump straight into the definition
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! # use self::Token::*;
//! # fn main() {
//! parse_rules! {
//!     term: Token;
//!
//!     zero_or_more: Vec<()> => {
//!         [Something, accumulator: zero_or_more] => {
//!             let mut acc = accumulator?;
//!             acc.push(());
//!             acc
//!         },
//!         [@] => Vec::new()
//!     }
//! }
//! # }
//! ```
//!
//! The `zero_or_more` nonterminal will give us a vector of the items we've matched or an empty
//! vector if none. The catch is that the resulting vector will be in a reverse order of what we
//! want since it uses recursion backtracking to accumulate the items. To handle this situation
//! we can use one of these approaches:
//!
//! * Insert the items at the beginning of the vector which will have a time complexity of `O(n^2)`.
//! * Have a second nonterminal dedicated to calling this one and reversing the result.
//! This one is faster than the previous one being `O(n)`.
//! * Use a special syntax to avoid recursion and use a loop internally. `O(n)` time complexity again
//! but without stack overflows.
//!
//! This third approach can be achieved with
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! # enum Token { Something }
//! # use self::Token::*;
//! # fn main() {
//! parse_rules! {
//!     term: Token;
//!
//!     #[fold(acc)]
//!     zero_or_more: Vec<()> => {
//!         [Something] => {
//!             acc.push(());
//!             acc
//!         },
//!         [@] => Vec::new()
//!     }
//! }
//! # }
//! ```
//!
//! As a result it will use way less stack frames and contain the items in the right order.
//! Win-win situation. Doing a little bit of code patter matching we can see that we've replaced
//! the call to the nonterminal with a `#[fold(acc)]` and no longer have to handle the parse result.
//! The `acc` can be any identifier we want to name our accumulator variable and it's always
//! mutable.
//!
//! The down side of this is that we can't have multiple arms in the nonterminal.
//! This might be improved in later versions of the crate. Right now it takes exactly one matching
//! arm and an epsilon arm which is the starting value of the accumulator.
//!
//! ### One or more
//!
//! As opposing to the last section this one is pretty obvious
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! # enum Token { Something }
//! # use self::Token::*;
//! # fn main() {
//! parse_rules! {
//!     term: Token;
//!
//!     one_or_more: Vec<()> => {
//!         [Something, zom: zero_or_more] => {
//!             let mut zom = zom?;
//!             zom.insert(0, ());
//!             zom
//!         }
//!     },
//!
//!     #[fold(acc)]
//!     zero_or_more: Vec<()> => {
//!         [Something] => {
//!             acc.push(());
//!             acc
//!         },
//!         [@] => Vec::new()
//!     }
//! }
//! # }
//! ```
//!
//! Some computational time could be save by creating a vector with expected or averaged capacity
//! and inserting a `mem::uninitialized` element before pushing the folded elements. Then the
//! first element that is matched in `one_or_more` can be inserted into the vector with
//! `mem:replace` and we must `mem::forget` the element returned from the replace to prevent Rust
//! from dropping an uninitialized value. This is an advanced approach so if you're not familiar
//! with what the functions do you can go and read on them in the Rust docs. In later versions of
//! the crate this construct could receive it's own syntax for convenience.
//!
//! ### Synopsis
//!
//! Usually handling these compositions in real situations might be a bit more complex but the
//! examples should have given you a good idea on how to approach such definitions.
//!
//! # Binary operators and precedence
//!
//! In this section we'll see how to define infix binary operators. This is always a bit of a
//! hustle to define by hand so the macro provides a syntax for that as well.
//!
//! Without going through all the trial and error examples lets jump straight into the working
//! definition
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! # fn main() {
//! enum Ast {
//!     BinOp(String, Box<Ast>, Box<Ast>),
//!     Number(u32)
//! }
//!
//! impl Ast {
//!     fn binop(op: &str, lhs: Ast, rhs: Ast) -> Self {
//!         Ast::BinOp(op.to_string(), Box::new(lhs), Box::new(rhs))
//!     }
//! }
//!
//! parse_rules! {
//!     term: &'static str;
//!
//!     #[binop(infix)]
//!     expr: Ast => _expr: Ast where precedence: u32 => |lhs, rhs| {
//!         &"=="  | 0 => Ast::binop("eq", lhs, rhs),
//!         &"!="  | 0 => Ast::binop("neq", lhs, rhs),
//!         &"+"   | 1 => Ast::binop("add", lhs, rhs),
//!         &"-"   | 1 => Ast::binop("sub", lhs, rhs),
//!         &"*"   | 2 => Ast::binop("mul", lhs, rhs),
//!         &"/"   | 2 => Ast::binop("div", lhs, rhs),
//!     },
//!
//!     _expr: Ast => {
//!         ["7"] => Ast::Number(7)
//!     },
//! }
//! # }
//! ```
//!
//! Well this is a complex one... Lets break it down.
//!
//! Firstly `#[binop(infix)]` triggers the special syntax.
//! Then there are three things to observe:
//!
//! * naming the nonterminal and giving it a type `expr: (String, i32, i32)`
//! * giving the name of the nonterminal used for the left and right-hand-sides `_expr`.
//! * declaring the precedence type as `u32`. The `precedence` word can be any other identifier.
//! It does not make any difference and is only there for cosmetics. The type can be anything with
//! ordering but stick to unsigned integers preferably.
//!
//! After that we get to the actual rules. The closure looking syntax describes how to handle the
//! different operators. `lhs` and `rhs` can be any identifiers and are respectively the
//! left-hand-side and the right-hand-side of the operator. The 'body' contains some `match` looking
//! arms with the difference that we use `| <value>` which states the operator precedence. Lower
//! precedence means that the operator will be processed later than operators with higher
//! precedence.
//!
//! Notice the `&`s. This is because the internals take references to the original terms.
//!
//! # Unary operators
//!
//! Defining unary operators is fairly simple. The only thing to consider is giving them precedence
//! but that can be achieved by nonterminal call arrangements. Lets take a look
//!
//! ### Prefix unary operators
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! # fn main() {
//! parse_rules! {
//!     term: &'static str;
//!
//!     not: bool => {
//!         ["!", expr: expr] => !(expr?)
//!     },
//!
//!     expr: bool => {
//!         ["true"] => true,
//!         ["false"] => false,
//!     },
//! }
//! # }
//! ```
//!
//! ### Postfix unary operators
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! # fn main() {
//! parse_rules! {
//!     term: &'static str;
//!
//!     maybe: bool => {
//!         [expr: expr, "?"] => (expr?).is_ok()
//!     },
//!
//!     expr: Result<(), ()> => {
//!         ["Ok"] => Ok(()),
//!         ["Err"] => Err(()),
//!     },
//! }
//! # }
//! ```
//!
//! # Custom handlers
//!
//! In the end if we want to create our own custom nonterminal we can use this special syntax
//!
//! ```
//! # #[macro_use]
//! # extern crate lexpar;
//! # fn main() {
//! parse_rules! {
//!     term: ();
//!
//!     my_handler: () => |iter| {
//!         /* handler logic goes here */
//!         Ok(())
//!     }
//! }
//! # }
//! ```
//!
//! The `iter` is a mutable reference to the `UnshiftableIter` that the internals use.
//! As opposing to the normal nonterminals we need to wrap our result in `Ok` or `Err` which gives
//! us control over the error handling.
//!
//! # Debugging
//!
//! As one of the future goals for the crate is to have a parser debug mode to know what exactly
//! failed and where. This would lower the time spent on debugging your grammar.
//!
//! For now here are some approaches to making debugging more pleasant:
//!
//! ### Common mistakes
//!
//! * Forgotten commas (`,`) between rules or nonterminals
//! * Forgotten arrows (`=>`)
//!
//! ### EchoIterator
//!
//! You can create an echo iterator with a simple map to print each term that is used
//!
//! ```ignore
//! iter.map(|term| {
//!     println!("{:?}", term);
//!     term
//! })
//! ```
//!
//! ### Last resort
//!
//! In case you can't figure out where the macro is failing at compile time as an addition to the
//! standard macro debugging approaches you can copy and paste the whole `parse_rules` macro into
//! the file where you use it and see where the macro error is located at. This will give you a bit
//! more descriptive compile errors instead of `the macro failed in that crate` kind of errors.
//!
//! # Examples
//!
//! Run the example projects with `cargo run --example <name>` where name is `ml` or `rust`.
//!
//! Some more examples can be found under the form of integration tests.
//!

use std::iter::Peekable;

/// Common errors that occur during parsing.
///
/// The nonterminals generated by `parse_rules` handle these errors by default.
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError<T> {
    UnexpectedRoot,
    Unexpected(T),
    Eof,
}

/// The result type returned by any nonterminal.
pub type Result<P, T> = ::std::result::Result<P, ParseError<T>>;

/// Unshiftable interator.
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
/// The macro does not yet account for:
///
/// * Left Factoring (`A -> qB | qC`)
/// * Left Recursion (`A -> Aq` (direct) and `A -> Bq B -> Ar` (indirect))
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
            // `iter` is necessary to be passed so that each arm has iter in its macro scope
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
