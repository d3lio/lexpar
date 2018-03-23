pub mod token;

use lexpar::lexer::{Lexer, Span};
use self::token::Token;

pub type Term = (Span, Token);

pub fn lexer() -> Lexer<(Span, Token)> {
    use self::Token::*;

    Lexer::new(lex_rules![
        r"[ \t\n]+"                 => |span, text, _| (span, Whitespace(text.to_owned())),
        r"/\*[^(?:*/)]*\*/"         => |span, text, _| (span, Comment(text[2..text.len() - 2].to_owned())),
        r"//[^\n]*"                 => |span, text, _| (span, Comment(text[2..].to_owned())),

        r"fn"                       => |span, _, _| (span, KwFn),
        r"let"                      => |span, _, _| (span, KwLet),
        r"if"                       => |span, _, _| (span, KwIf),
        r"then"                     => |span, _, _| (span, KwThen),
        r"else"                     => |span, _, _| (span, KwElse),
        r"for"                      => |span, _, _| (span, KwFor),
        r"in"                       => |span, _, _| (span, KwIn),
        r"do"                       => |span, _, _| (span, KwDo),
        r"or"                       => |span, _, _| (span, KwOr),
        r"and"                      => |span, _, _| (span, KwAnd),

        r"[_a-zA-Z][_a-zA-Z0-9]*"   => |span, text, _| (span, Ident(text.to_owned())),
        r"-?[0-9]+(?:\.[0-9]+)?"    => |span, text, _| (span, Number(text.parse().unwrap())),

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
        r"\.\."                     => |span, _, _| (span, DoubleDot),

        r"!"                        => |span, _, _| (span, Excl),

        r"->"                       => |span, _, _| (span, Arrow),
        r"="                        => |span, _, _| (span, Assign),
        r":"                        => |span, _, _| (span, Colon),
        r","                        => |span, _, _| (span, Comma),
        r"\|"                       => |span, _, _| (span, Pipe),
        r";"                        => |span, _, _| (span, Semicolon),
        r"'(?:\\'|[^'])*'"          => |span, text, _| (span, SingleQuote(text[1..(text.len()-1)].to_owned())),
        r#""(?:\\"|[^"])*""#        => |span, text, _| (span, DoubleQuote(text[1..(text.len()-1)].to_owned())),
    ], |span, text| (span, Unknown(text.to_owned())))
}
