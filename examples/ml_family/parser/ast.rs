use std::fmt::{self, Debug, Formatter};

use lexpar::lexer::Span;

pub trait Ast: Debug {}

pub struct AstNode {
    pub span: Span,
    expr: Box<Ast>
}

impl AstNode {
    pub fn new<A>(span: Span, expr: A) -> Self where A: Ast + 'static {
        Self {
            span,
            expr: Box::new(expr)
        }
    }
}

impl Debug for AstNode {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self.expr))
    }
}

#[derive(Debug)]
pub enum BinOp {
    Eq,
    NotEq,
    Add,
    Sub,
    Mul,
    Div,
}

macro_rules! ast_nodes {
    {
        $(struct $name: ident {
            $( $field: ident : $type: ty ),* $(,)*
        })+
    } => {
        $(
            #[derive(Debug)]
            pub struct $name {
                $( pub $field: $type ),*
            }
            impl Ast for $name {}
        )+
    }
}

ast_nodes! {
    struct NumberExpr {
        num: f64
    }

    struct VariableExpr {
        name: String
    }

    struct FunctionProtoExpr {
        name: Option<String>,
        params: Vec<String>
    }

    struct FunctionExpr {
        proto: AstNode,
        body: AstNode
    }

    struct ClosureExpr {
        proto: AstNode,
        body: AstNode
    }

    struct CallExpr {
        name: String,
        args: Vec<AstNode>
    }

    struct BlockExpr {
        exprs: Vec<AstNode>
    }

    struct BinExpr {
        op: BinOp,
        lhs: AstNode,
        rhs: AstNode
    }

    struct IfExpr {
        cond: AstNode,
        then: AstNode,
        el: Option<AstNode>
    }

    struct VariableDef {
        name: String,
        value: AstNode
    }
}