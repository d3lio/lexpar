pub mod ast;

mod transform;

use lexpar::lexer::{LexIter, Span};

use ml_family::lexer::Term;
use ml_family::lexer::token::Token;
use ml_family::lexer::token::Token::*;

use self::transform::BlockIterator;

use self::ast::{
    AstNode,
    BinOp,
    NumberExpr,
    VariableExpr,
    FunctionProtoExpr,
    FunctionExpr,
    ClosureExpr,
    CallExpr,
    BlockExpr,
    BinExpr,
    IfExpr,
    VariableDef
};

type Result = ::lexpar::parser::Result<Vec<AstNode>, Term>;

pub struct Parser;

impl Parser {
    pub fn parse(iter: LexIter<Term>) -> Result {
        let iter = iter.blocks().filter(|x| match *x {
            (_, Token::Whitespace(_)) => false,
            (_, Token::Comment(_)) => false,
            _ => true
        });

        top_level(&mut iter.into())
    }
}

macro_rules! span {
    ($astl: expr, $astr: expr) => {
        Span::new($astl.span.lo, $astr.span.hi, $astl.span.line)
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
            if let Some(node) = node? {
                nodes.push(node);
            }
            nodes
        },
        [@] => Vec::new()
    },

    _top_level: Option<AstNode> => {
        [def: def] => Some(def?),
        [expr: expr] => Some(expr?),
        [(_, Delimiter)] => None
    }
}

// Definition and expression parsing
parse_rules! {
    term: Term;

    def: AstNode => {
        // Variable definition
        [(span, KwLet), (_, Ident(name)), (_, Assign), ex: expr] => {
            let ex = ex?;
            ast!(span.extend(ex.span.hi), VariableDef { name, value: ex })
        },

        // Function definition
        [proto: prototype, body: expr] => {
            let proto = proto?;
            let body = body?;
            let span = proto.span.clone().extend(body.span.hi);
            ast!(span, FunctionExpr { proto, body })
        }
    },

    #[binop(infix)]
    expr: AstNode => _expr: AstNode where precedence: u32 => |lhs, rhs| {
        &(_, Eq)         | 0 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Eq, lhs, rhs }),
        &(_, NotEq)      | 0 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::NotEq, lhs, rhs }),
        &(_, Plus)       | 1 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Add, lhs, rhs }),
        &(_, Minus)      | 1 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Sub, lhs, rhs }),
        &(_, Asterisk)   | 2 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Mul, lhs, rhs }),
        &(_, FSlash)     | 2 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Div, lhs, rhs }),
    },

    _expr: AstNode => {
        [ex: __expr] => ex?,

        // Closure definition
        [(mut lspan, Pipe), params: params, (rspan, Pipe), body: expr] => {
            lspan.hi = rspan.hi;
            let proto = ast!(lspan.clone(), FunctionProtoExpr { name: None, params: params? });
            let body = body?;
            lspan.hi = body.span.hi;
            ast!(lspan, ClosureExpr { proto, body })
        },

        [(mut span, KwIf), cond: expr, (_, KwThen), then: expr, el: _else] => {
            let cond = cond?;
            let then = then?;
            let el = el?;
            if let Some(el) = el {
                span.hi = el.span.hi;
                ast!(span, IfExpr { cond, then, el: Some(el) })
            } else {
                span.hi = then.span.hi;
                ast!(span, IfExpr { cond, then, el: None })
            }
        },

        // Block expression
        [(mut lspan, BlockStart), top: top_level, (rspan, BlockEnd)] => {
            lspan.hi = rspan.hi;
            ast!(lspan, BlockExpr { exprs: top? })
        },

        // Variable expression or function call
        [(mut span, Ident(name)), args: call] => {
            if let Some((call_span, args)) = args? {
                span.hi = call_span.hi;
                ast!(span, CallExpr { name, args })
            } else {
                ast!(span, VariableExpr { name })
            }
        },
    },

    __expr: AstNode => {
        // Paren expression
        [(_, LParen), ex: expr, (_, RParen)] => ex?,

        // Literal expression
        [literal: literal] => literal?,
    },

    literal: AstNode => {
        // Number literal
        [(span, Number(num))] => ast!(span, NumberExpr { num }),
    }
}

// Variable expression or function invocation
parse_rules! {
    term: Term;

    // Variable expression or function call
    call: Option<(Span, Vec<AstNode>)> => {
        [args: args] => {
            let args = args?;
            if !args.is_empty() {
                let span = args[0].span.clone().extend(args.last().unwrap().span.hi);
                Some((span, args))
            } else {
                None
            }
        },
        [@] => None
    },

    // Function call arguments
    #[fold(args)]
    args: Vec<AstNode> => {
        [ex: arg] => {
            args.push(ex?);
            args
        },
        [@] => Vec::new()
    },

    arg: AstNode => {
        [ex: __expr] => ex?,

        // Variable expression
        [(span, Ident(name))] => ast!(span, VariableExpr { name })
    },
}

// Functions
parse_rules! {
    term: Term;

    // Function prototype
    prototype: AstNode => {
        [
            (mut lspan, KwFn),
            (_, Ident(name)),
            params: params,
            (rspan, Assign)
        ] => {
            lspan.hi = rspan.hi;
            ast!(lspan, FunctionProtoExpr { name: Some(name), params: params? })
        }
    },

    // Function parameters
    #[fold(params)]
    params: Vec<String> => {
        [(_, Ident(name))] => {
            params.push(name);
            params
        },
        [@] => Vec::new()
    },
}

// Ifs
parse_rules! {
    term: Term;

    _else: Option<AstNode> => {
        [(_, KwElse), ex: expr] => Some(ex?),
        [@] => None
    }
}
