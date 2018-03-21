pub mod ast;

use lexpar::lexer::{LexIter, Span};

use rust_family::lexer::token::{Kw, Token};
use rust_family::lexer::token::Token::*;

use self::ast::{
    AstNode,
    BinOp,
    NumberExpr,
    VariableExpr,
    FunctionProtoExpr,
    FunctionExpr,
    CallExpr,
    BinExpr,
    VariableDefExpr
};

type Term = (Span, Token);
type Result = ::lexpar::parser::Result<Vec<AstNode>, Term>;

pub struct Parser;

impl Parser {
    pub fn parse(iter: LexIter<Term>) -> Result {
        let iter = iter.filter(|x| match *x {
            (_, Token::Whitespace(_)) => false,
            (_, Token::Comment(_)) => false,
            _ => true
        });

        top_level(&mut iter.into())
    }
}

macro_rules! span {
    ($astl: expr, $astr: expr) => {
        Span::new($astl.span().lo, $astr.span().hi, $astl.span().line)
    };
}

macro_rules! ast {
    ($span: expr, $ast_expr: expr) => {
        AstNode::new($span, $ast_expr)
    };
}

parse_rules! {
    term: Term;

    #[fold(nodes)]
    top_level: Vec<AstNode> => {
        [node: _top_level] => {
            nodes.push(node);
            nodes
        },
        [@] => Vec::new()
    },

    _top_level: AstNode => {
        [def: def] => def,
        [expr: expr] => expr
    }
}

// Definition and expression parsing
parse_rules! {
    term: Term;

    def: AstNode => {
        // Variable definition
        [(span, Keyword(Kw::Let)), (_, Ident(name)), (_, Assign), ex: expr, (_, Semicolon)] => {
            ast!(span.extend(ex.span().hi), VariableDefExpr { name, value: ex })
        }
    },

    #[binop(infix)]
    expr: AstNode => _expr where u32 => |lhs, rhs| {
        &(_, Eq)         | 0 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Eq, lhs, rhs }),
        &(_, NotEq)      | 0 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::NotEq, lhs, rhs }),
        &(_, Plus)       | 1 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Add, lhs, rhs }),
        &(_, Minus)      | 1 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Sub, lhs, rhs }),
        &(_, Asterisk)   | 2 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Mul, lhs, rhs }),
        &(_, FSlash)     | 2 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Div, lhs, rhs }),
    },

    _expr: AstNode => {
        // Number expression
        [(span, Number(num))] => ast!(span, NumberExpr { num }),

        // Paren expression
        [(_, LParen), ex: expr, (_, RParen)] => ex,

        // Variable expression or function call
        [(mut span, Ident(name)), args: call] => {
            if let Some((call_span, args)) = args {
                span.hi = call_span.hi;
                ast!(span, CallExpr { name, args })
            } else {
                ast!(span, VariableExpr { name })
            }
        },

        // Function definition
        [proto: fn_proto, (_, LBrace), body: top_level, (rspan, RBrace)] => {
            ast!(proto.span().clone().extend(rspan.hi), FunctionExpr { proto, body: body })
        }
    },
}

// Variable expression or function invocation
parse_rules! {
    term: Term;

    // Variable expression or function call
    call: Option<(Span, Vec<AstNode>)> => {
        [(span, LParen), args: args, (rspan, RParen)] => {
            Some((span.extend(rspan.hi), args))
        },
        [@] => None
    },

    // Function call arguments
    args: Vec<AstNode> => {
        [ex: expr, args: _args] => {
            let mut args = args;
            use std::mem;
            mem::forget(mem::replace(&mut args[0], ex));
            args
        },
        [@] => Vec::new()
    },

    #[fold(args)]
    _args: Vec<AstNode> => {
        [(_, Comma), ex: expr] => {
            args.push(ex);
            args
        },
        [@] => {
            let mut acc = Vec::with_capacity(8);
            unsafe { acc.push(::std::mem::uninitialized()) }
            acc
        }
    },
}

// Functions
parse_rules! {
    term: Term;

    // Function prototype
    fn_proto: AstNode => {
        [
            (span, Keyword(Kw::Fn)),
            (_, Ident(name)),
            (_, LParen),
            params: params,
            (rspan, RParen)
        ] => {
            ast!(span.extend(rspan.hi), FunctionProtoExpr { name, params: params })
        }
    },

    // Function prototype params
    params: Vec<String> => {
        [(_, Ident(name)), params: _params] => {
            let mut params = params;
            params[0] = name;
            params
        },
        [@] => Vec::new()
    },

    #[fold(params)]
    _params: Vec<String> => {
        [(_, Comma), (_, Ident(name))] => {
            params.push(name);
            params
        },
        [@] => vec![String::new()]
    },
}
