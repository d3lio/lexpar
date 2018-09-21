pub mod ast;

mod transform;

use lexpar::lexer::{LexIter, Span};
use lexpar::parser::ParseError;

use ml_family::lexer::Term;
use ml_family::lexer::token::Token;
use ml_family::lexer::token::Token::*;

use self::transform::BlockIterator;

use self::ast::*;

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

    top_level: Vec<AstNode> => |iter| {
        let items = _top_level(iter)?;

        // Explicit error handling because fold never fails with UnexpectedRoot because it must act
        // as a Kleene star but in this case we keep matching until eof otherwise it's an error
        if iter.peek().is_some() {
            Err(ParseError::UnexpectedRoot)
        } else {
            Ok(items)
        }
    },

    #[fold(nodes)]
    _top_level: Vec<AstNode> => {
        [node: __top_level] => {
            if let Some(node) = node {
                nodes.push(node);
            }
            nodes
        },
        [@] => Vec::new()
    },

    __top_level: Option<AstNode> => {
        [def: def] => Some(def),
        [expr: expr] => Some(expr),
        [(_, BlockCont)] => None
    },
}

// Definition and expression parsing
parse_rules! {
    term: Term;

    def: AstNode => {
        // Variable definition
        [(span, KwLet), (_, Ident(name)), (_, Assign), ex: expr] => {
            ast!(span.extend(ex.span.hi), VariableDef { name, value: ex })
        },

        // Function definition
        [proto: prototype, body: expr] => {
            let span = proto.span.clone().extend(body.span.hi);
            ast!(span, FunctionExpr { proto, body })
        }
    },

    #[binop(infix)]
    expr: AstNode => _expr where u32 => |lhs, rhs| {
        &(_, Assign)     | 0 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Assign, lhs, rhs }),
        &(_, KwOr)       | 1 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Or, lhs, rhs }),
        &(_, KwAnd)      | 1 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::And, lhs, rhs }),
        &(_, Eq)         | 2 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Eq, lhs, rhs }),
        &(_, NotEq)      | 2 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::NotEq, lhs, rhs }),
        &(_, DoubleDot)  | 3 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Range, lhs, rhs }),
        &(_, Plus)       | 4 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Add, lhs, rhs }),
        &(_, Minus)      | 4 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Sub, lhs, rhs }),
        &(_, Asterisk)   | 5 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Mul, lhs, rhs }),
        &(_, FSlash)     | 5 => ast!(span!(lhs, rhs), BinExpr { op: BinOp::Div, lhs, rhs }),
    },

    _expr: AstNode => {
        [ex: __expr] => ex,

        // Closure definition
        [(mut lspan, Pipe), params: params, (rspan, Pipe), body: expr] => {
            lspan.hi = rspan.hi;
            let proto = ast!(lspan.clone(), FunctionProtoExpr { name: None, params: params });
            lspan.hi = body.span.hi;
            ast!(lspan, ClosureExpr { proto, body })
        },

        // If expression
        [(mut span, KwIf), cond: expr, (_, KwThen), then: expr, el: _else] => {
            if let Some(el) = el {
                span.hi = el.span.hi;
                ast!(span, IfExpr { cond, then, el: Some(el) })
            } else {
                span.hi = then.span.hi;
                ast!(span, IfExpr { cond, then, el: None })
            }
        },

        // For expression
        [(mut span, KwFor), (vspan, Ident(var)), (_, KwIn), iter: expr, (_, KwDo), body: expr] => {
            span.hi = body.span.hi;
            let var = ast!(vspan, VariableExpr { name: var });
            ast!(span, ForExpr { var, iter: iter, body })
        },

        // Block expression
        [(mut lspan, BlockStart), top: _top_level, (rspan, BlockEnd)] => {
            lspan.hi = rspan.hi;
            ast!(lspan, BlockExpr { exprs: top })
        },

        // Variable expression or function call
        [(mut span, Ident(name)), args: call] => {
            if let Some((call_span, args)) = args {
                span.hi = call_span.hi;
                ast!(span, CallExpr { name, args })
            } else {
                ast!(span, VariableExpr { name })
            }
        },
    },

    __expr: AstNode => {
        // Paren expression
        [(_, LParen), ex: expr, (_, RParen)] => ex,

        // Literal expression
        [literal: literal] => literal,
    },

    literal: AstNode => {
        // Number literal
        [(span, Number(num))] => ast!(span, NumberExpr { num }),

        // String literal
        [(span, SingleQuote(string))] => ast!(span, StringExpr { string }),

        // String literal
        [(span, DoubleQuote(string))] => ast!(span, StringExpr { string }),
    },
}

// Variable expression or function invocation
parse_rules! {
    term: Term;

    // Variable expression or function call
    call: Option<(Span, Vec<AstNode>)> => {
        [args: args] => {
            if !args.is_empty() {
                let span = args[0].span.clone().extend(args.last().unwrap().span.hi);
                Some((span, args))
            } else {
                None
            }
        }
    },

    // Function call arguments
    #[fold(args)]
    args: Vec<AstNode> => {
        [ex: arg] => {
            args.push(ex);
            args
        },
        [@] => Vec::new()
    },

    arg: AstNode => {
        [ex: __expr] => ex,

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
            ast!(lspan, FunctionProtoExpr { name: Some(name), params: params })
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
        [(_, KwElse), ex: expr] => Some(ex),
        [@] => None
    },
}
