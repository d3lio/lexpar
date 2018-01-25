#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    // Not code
    Whitespace(String),
    Comment(String),

    // Keywords
    KwFn,
    KwLet,
    KwIf, KwThen, KwElse,
    // KwFor, KwIn, KwDo,

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

    // Unary Operators
    Excl,

    // Misc Operators
    Arrow,
    Assign,
    Colon,
    Comma,
    Pipe,
    Semicolon,

    // Control (non-lex tokens)

    BlockStart, BlockEnd,
    Delimiter,

    Unknown(String)
}
