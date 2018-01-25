#[derive(Clone, Debug, PartialEq)]
pub enum Kw {
    Fn,
    Let
}

impl Kw {
    pub fn pattern() -> &'static str {
        "fn|let"
    }
}

impl<'a> ::std::convert::From<&'a str> for Kw {
    fn from(s: &'a str) -> Kw {
        match s {
            "fn" => Kw::Fn,
            "let" => Kw::Let,
            _ => unreachable!()
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Whitespace(String),
    Comment(String),

    Keyword(Kw),
    Ident(String),

    Number(f64),

    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,

    Plus,
    Minus,
    Asterisk,
    FSlash,
    Eq,
    NotEq,

    Assign,
    Excl,

    Colon,
    Semicolon,
    Comma,
    Arrow,

    Unknown(String)
}
