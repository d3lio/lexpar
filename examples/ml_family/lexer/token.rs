#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    // Not code
    Whitespace(String),
    Comment(String),

    // Keywords
    KwFn,
    KwLet,
    KwIf, KwThen, KwElse,
    KwFor, KwIn, KwDo,
    KwOr, KwAnd,

    // Data
    Ident(String),
    Number(f64),

    // Brackets
    LParen, RParen,
    LBracket, RBracket,
    LBrace, RBrace,

    // Binary Operators
    Plus, Minus,
    Asterisk, FSlash,
    Eq, NotEq,
    DoubleDot,

    // Unary Operators
    Excl,

    // Misc Operators
    Arrow,
    Assign,
    Colon,
    Comma,
    Pipe,
    Semicolon,
    SingleQuote(String),
    DoubleQuote(String),

    // Control (non-lex tokens)

    BlockStart, BlockEnd, BlockCont,

    Unknown(String)
}
