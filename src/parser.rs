//! The `Parser` module holds simple structures for token parsing.
//!
//! This probably won't be the final parser and thus nothing in this module is documented yet.

use std::collections::HashMap;
use std::hash::Hash;
use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError<T> {
    Unexpected(T),
    Eof
}

pub struct Callback<T, N, A>(
    pub Box<Fn(
        &HashMap<N, Callback<T, N, A>>,
        &mut Peekable<Box<Iterator<Item = T>>>
    ) -> A>
);

pub struct Parser<T, N, A> {
    rules: HashMap<N, Callback<T, N, A>>
}

impl<T, N, A> Parser<T, N, A> where N: PartialEq + Eq + Hash {
    pub fn new() -> Self {
        Self {
            rules: HashMap::new()
        }
    }

    /// See `HashMap::insert`
    pub fn rule<F>(&mut self, nonterm: N, rule: F) -> Option<Callback<T, N, A>>
    where F: 'static + Fn(&HashMap<N, Callback<T, N, A>>, &mut Peekable<Box<Iterator<Item = T>>>) -> A {
        self.rules.insert(nonterm, Callback(Box::new(rule)))
    }

    pub fn gen<I>(&mut self, iter: I, top: &N) -> A where I: 'static + Iterator<Item = T> {
        (self.rules.get(top).unwrap().0)(
            &self.rules,
            &mut (Box::new(iter) as Box<Iterator<Item = T>>).peekable()
        )
    }
}
