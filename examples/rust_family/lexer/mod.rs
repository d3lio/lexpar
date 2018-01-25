pub mod token;

use lexpar::lexer::{Lexer, Span};

use self::token::{Kw, Token};

pub fn lexer() -> Lexer<(Span, Token)> {
    use self::Token::*;

    Lexer::new(lex_rules![
        r"[ \t\n]+"                 => |text, span| (span, Whitespace(text.to_owned())),
        r"/\*[^(?:*/)]*\*/"         => |text, span| (span, Comment(text[2..text.len() - 2].to_owned())),
        r"//[^\n]*"                 => |text, span| (span, Comment(text[2..].to_owned())),
        Kw::pattern()               => |text, span| (span, Keyword(Kw::from(text))),
        r"[_a-zA-Z][_a-zA-Z0-9]*"   => |text, span| (span, Ident(text.to_owned())),
        r"-?[0-9]+(?:\.[0-9]*)?"    => |text, span| (span, Number(text.parse().unwrap())),
        r"\("                       => |_, span| (span, LParen),
        r"\)"                       => |_, span| (span, RParen),
        r"\["                       => |_, span| (span, LBracket),
        r"\]"                       => |_, span| (span, RBracket),
        r"\{"                       => |_, span| (span, LBrace),
        r"\}"                       => |_, span| (span, RBrace),

        r"\+"                       => |_, span| (span, Plus),
        r"\-"                       => |_, span| (span, Minus),
        r"\*"                       => |_, span| (span, Asterisk),
        r"/"                        => |_, span| (span, FSlash),
        r"=="                       => |_, span| (span, Eq),
        r"!="                       => |_, span| (span, NotEq),

        r"!"                        => |_, span| (span, Excl),

        r":"                        => |_, span| (span, Colon),
        r";"                        => |_, span| (span, Semicolon),
        r","                        => |_, span| (span, Comma),
        r"="                        => |_, span| (span, Assign),
        r"->"                       => |_, span| (span, Arrow)
    ], |text, span| (span, Unknown(text.to_owned())))
}
