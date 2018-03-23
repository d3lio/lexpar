use std::cmp::Ordering;

use lexpar::lexer::{LexIter, Span};

use ml_family::lexer::Term;
use ml_family::lexer::token::Token;

impl Token {
    const TAB_SIZE: Depth = 4;

    pub fn parse_indent(&self) -> Option<u32> {
        if let &Token::Whitespace(ref string) = self {
            let mut chars = string.chars();
            if let Some('\n') = chars.next() {
                return Some(chars.fold(0, |acc, c| match c {
                    '\t' => acc + Self::TAB_SIZE,
                    ' ' => acc + 1,
                    _ => acc,
                }))
            }
        }

        None
    }
}

type Depth = u32;

pub trait BlockIterator {
    fn blocks(self) -> BlockIter;
}

impl BlockIterator for LexIter<Term> {
    fn blocks(self) -> BlockIter {
        BlockIter::new(self)
    }
}

pub struct BlockIter {
    iter: LexIter<Term>,
    blocks: Vec<Depth>,
    closing: u32,
    last_span: Option<Span>
}

impl BlockIter {
    pub fn new(iter: LexIter<Term>) -> Self {
        Self {
            iter,
            blocks: vec![0],
            closing: 0,
            last_span: None,
        }
    }
}

impl Iterator for BlockIter {
    type Item = Term;

    fn next(&mut self) -> Option<Self::Item> {
        if self.closing > 0 {
            self.closing -= 1;
            self.blocks.pop().unwrap();
            if let Some(ref span) = self.last_span {
                Some((Span::new(span.hi, span.hi, span.line), Token::BlockEnd))
            } else {
                None
            }
        } else {
            self.iter.next().map(|(span, token)| {
                let tok = if let Some(depth) = token.parse_indent() {
                    let last = self.blocks.last().unwrap().clone();
                    match depth.cmp(&last) {
                        Ordering::Equal => Token::BlockCont,
                        Ordering::Greater => {
                            self.blocks.push(depth);
                            Token::BlockStart
                        },
                        Ordering::Less => {
                            let closing = self.blocks
                                .iter()
                                .filter(|&&block| block > depth)
                                .count();

                            self.closing = closing as u32 - 1;
                            self.last_span = Some(span.clone());
                            self.blocks.pop().unwrap();
                            Token::BlockEnd
                        }
                    }
                } else {
                    token
                };

                (span, tok)
            })
        }
    }
}
