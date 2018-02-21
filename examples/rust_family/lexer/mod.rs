pub mod token;

use lexpar::lexer::{Lexer, Span};

use self::token::{Kw, Token};

pub fn lexer() -> Lexer<(Span, Token)> {
    use self::Token::*;

    Lexer::new(lex_rules![
        r"[ \t\n]+"                 => |span, text, _| (span, Whitespace(text.to_owned())),
        r"/\*[^(?:*/)]*\*/"         => |span, text, _| (span, Comment(text[2..text.len() - 2].to_owned())),
        r"//[^\n]*"                 => |span, text, _| (span, Comment(text[2..].to_owned())),
        Kw::pattern()               => |span, text, _| (span, Keyword(Kw::from(text))),
        r"[_a-zA-Z][_a-zA-Z0-9]*"   => |span, text, _| (span, Ident(text.to_owned())),
        r"-?[0-9]+(?:\.[0-9]*)?"    => |span, text, _| (span, Number(text.parse().unwrap())),
        r"\("                       => |span, _, _| (span, LParen),
        r"\)"                       => |span, _, _| (span, RParen),
        r"\["                       => |span, _, _| (span, LBracket),
        r"\]"                       => |span, _, _| (span, RBracket),
        r"\{"                       => |span, _, _| (span, LBrace),
        r"\}"                       => |span, _, _| (span, RBrace),

        r"\+"                       => |span, _, _| (span, Plus),
        r"\-"                       => |span, _, _| (span, Minus),
        r"\*"                       => |span, _, _| (span, Asterisk),
        r"/"                        => |span, _, _| (span, FSlash),
        r"=="                       => |span, _, _| (span, Eq),
        r"!="                       => |span, _, _| (span, NotEq),

        r"!"                        => |span, _, _| (span, Excl),

        r":"                        => |span, _, _| (span, Colon),
        r";"                        => |span, _, _| (span, Semicolon),
        r","                        => |span, _, _| (span, Comma),
        r"="                        => |span, _, _| (span, Assign),
        r"->"                       => |span, _, _| (span, Arrow)
    ], |span, text| (span, Unknown(text.to_owned())))
}
