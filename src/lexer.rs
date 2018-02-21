//! This module holds structures for parsing source into tokens.

use std::rc::Rc;
use std::borrow::Borrow;

use regex::Regex;

/// Helper macro for generating the `Lexer` rules.
///
/// See `Lexer` for more info.
#[macro_export]
macro_rules! lex_rules {
    ($($e: expr => $b: expr),+) => { vec![$( ($e, Box::new($b)) ),+] };
    ($($e: expr => $b: expr),+,) => { vec![$( ($e, Box::new($b)) ),+] };
}

/// Represents a range of characters in the source.
///
/// The `Span` holds a lo-hi position range as [lo, hi) and the line at which the match begins
/// to allow better error messages.
#[derive(Debug, Clone, PartialEq)]
pub struct Span {
    /// The position of the first char of the match.
    pub lo: usize,
    /// The position of the char after the last char of the match.
    pub hi: usize,
    /// The line on which the span starts i.e. the line which contains the `lo`th symbol.
    pub line: usize
}

impl Span {
    pub fn new(lo: usize, hi: usize, line: usize) -> Self {
        Self {
            lo: lo,
            hi: hi,
            line: line
        }
    }

    pub fn extend(mut self, hi: usize) -> Self {
        self.hi = hi;
        self
    }
}

struct Arm<T> {
    captures: usize,
    handle: Box<for<'a> Fn(Span, &'a str, Vec<&'a str>) -> T>
}

// TODO(low) remove this in favour of lifetimes.
struct LexerInternal<T> {
    matcher: Regex,
    arms: Vec<Arm<T>>,
    unknown: Box<for<'a> Fn(Span, &'a str) -> T>
}

/// Generic token lexer
///
/// When creating a `Lexer` it builds the token matcher out of the given rules (regexes).
///
/// Each time it matches a rule, the associated callback is called with matching text (`&str`) and a
/// `Span` which holds the start and end position as well as the line at which the first symbol was
/// found. In the callback the user can execute custom logic and return the corresponding token.
///
/// There is also the `unknown` callback which is invoked when non of the rules match. The first
/// argument is a `&str` which contains only the first erroneous char and a `Span`. The `Lexer`
/// expects that the user either panics in the unknown callback or returns a special token at which
/// point the `LexIter` will move the matching position 1 character forward so it can continue
/// matching after an error. The former behavior is more common as the only purpose of returning
/// a special erroneous token would be for generating better errors.
///
/// # Notes
///
/// The `Lexer` is just a builder for `LexIter`s which do the actual work.
///
/// # Examples
///
/// ```
/// # #[macro_use]
/// # extern crate lexpar;
/// # use lexpar::lexer::*;
/// enum Token {
///     Snake(String),
///     Int(u32)
/// }
///
/// # fn main() {
/// let lex = Lexer::new(lex_rules![
///     // snake_case
///     "[_a-z]+" => |span, text, _| (Token::Snake(text.to_owned()), span),
///     // integer
///     "[0-9]+" => |span, text, _| (Token::Int(text.parse().unwrap()), span)
/// ], |_, _| panic!("unknown"));
/// # }
/// ```
pub struct Lexer<T> {
    internal: Rc<LexerInternal<T>>
}

/// Token iterator over a given source.
///
/// To create a `LexIter` you need to call `Lexer::src_iter`.
///
/// This is the structure that operates over the source and matches the tokens.
/// As an ordinary `Iterator` invoking next will give you the next element of type T, presumably a
/// token or a structure containing the token.
pub struct LexIter<T> {
    internal: Rc<LexerInternal<T>>,
    src: String,
    pos: usize,
    line: usize
}

impl<T> Lexer<T> {
    /// Create a new lexer with the given `rules` and `unknown` token callback.
    pub fn new<F>(rules: Vec<(&str, Box<for<'a> Fn(Span, &'a str, Vec<&'a str>) -> T>)>, unknown: F) -> Self
    where F: 'static + for<'a> Fn(Span, &'a str) -> T {
        if rules.is_empty() {
            panic!("Empty rules set");
        }

        let (pattern, arms) = {
            let mut pattern = String::new();
            let mut arms = Vec::new();
            let mut rules_iter = rules.into_iter();

            if let Some((pat, handle)) = rules_iter.next() {
                let captures = Regex::new(pat).unwrap().captures_len();
                pattern.push_str(&format!("({})", pat));
                arms.push(Arm { captures, handle });

                for (pat, handle) in rules_iter {
                    let captures = Regex::new(pat).unwrap().captures_len();
                    pattern.push_str(&format!("|({})", pat));
                    arms.push(Arm { captures, handle });
                }
            }

            (format!("^(?:{})", pattern), arms)
        };

        Self {
            internal: Rc::new(LexerInternal {
                matcher: Regex::new(&pattern).unwrap(),
                arms: arms,
                unknown: Box::new(unknown)
            })
        }
    }

    /// Create a token iterator out of a given source.
    pub fn src_iter<S: Borrow<str>>(&self, src: S) -> LexIter<T> {
        LexIter {
            internal: self.internal.clone(),
            src: src.borrow().to_owned(),
            pos: 0,
            line: 0
        }
    }
}

impl<T> Iterator for LexIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.pos >= self.src.len() {
            return None;
        }

        let res = if let Some(caps) = self.internal.matcher.captures(&self.src[self.pos..]) {
            let (pos, arm) = {
                // skip 0th capture since it corresponds to the whole regex capture
                let mut pos = 1;
                let mut arm = None;
                for a in &self.internal.arms {
                    if caps.get(pos).is_some() {
                        arm = Some(a);
                        break;
                    }
                    pos += a.captures;
                };
                (pos, arm.unwrap())
            };

            let mat = caps.get(pos).unwrap();
            let text = mat.as_str();
            let prev_line = self.line;
            let prev_pos = self.pos;

            self.line += text.chars().filter(|&x| x == '\n').count();
            self.pos += mat.end();

            let span = Span {
                lo: prev_pos,
                hi: self.pos,
                line: prev_line
            };

            let subcaptures: Vec<_> = (1..arm.captures)
                .map(|idx| caps.get(idx + pos).unwrap().as_str())
                .collect();

            (arm.handle)(span, text, subcaptures)
        } else {
            self.pos += 1;
            let span = Span {
                lo: self.pos - 1,
                hi: self.pos,
                line: self.line
            };
            (self.internal.unknown)(span, &self.src[(self.pos - 1)..self.pos])
        };

        Some(res)
    }
}
