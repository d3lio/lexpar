#[macro_use]
extern crate lexpar;

use lexpar::lexer::Lexer;

#[derive(Debug, PartialEq)]
enum Kw {
    Fn,
    Let
}

impl Kw {
    fn pattern() -> &'static str {
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

#[derive(Debug, PartialEq)]
enum Token {
    Whitespace(String),
    Comment(String),
    Keyword(Kw),
    Ident(String),
    Float(f32),
    Integer(i32),
    Text(String),
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
    Arrow,
    Assign,
    Unknown(String)
}
use self::Token::*;

#[test]
fn some_tokens() {
    let lex = Lexer::new(lex_rules![
        r"[ \t\n]+"                 => |span, text, _| (span, Whitespace(text.to_owned())),
        r"/\*[^(?:*/)]*\*/"         => |span, text, _| (span, Comment(text[2..text.len() - 2].to_owned())),
        r"//[^\n]*"                 => |span, text, _| (span, Comment(text[2..].to_owned())),
        Kw::pattern()               => |span, text, _| (span, Keyword(Kw::from(text))),
        r"[_a-zA-Z][_a-zA-Z0-9]*"   => |span, text, _| (span, Ident(text.to_owned())),
        r"-?[0-9]+\.[0-9]*"         => |span, text, _| (span, Float(text.parse().unwrap())),
        r"-?[0-9]+"                 => |span, text, _| (span, Integer(text.parse().unwrap())),
        r#""(.*)""#                 => |span, _, caps| (span, Text(caps[0].to_owned())),
        r"->"                       => |span, _, _| (span, Arrow),
        r"="                        => |span, _, _| (span, Assign),
        r"\("                       => |span, _, _| (span, LParen),
        r"\)"                       => |span, _, _| (span, RParen),
        r"\["                       => |span, _, _| (span, LBracket),
        r"\]"                       => |span, _, _| (span, RBracket),
        r"\{"                       => |span, _, _| (span, LBrace),
        r"\}"                       => |span, _, _| (span, RBrace),
        r"\+"                       => |span, _, _| (span, Plus),
        r"\-"                       => |span, _, _| (span, Minus),
        r"\*"                       => |span, _, _| (span, Asterisk),
        r"/"                        => |span, _, _| (span, FSlash)
    ], |span, text| (span, Unknown(text.to_owned())));

    let tokens = lex.src_iter(
        r#"
        {*/}[+(he
        _llo)-12.5h3]/*multi
        line
        comment
        */
        "string"
        -10 5
        //hello fdsf
        //|
        "#).collect::<Vec<_>>();

    assert_eq!(tokens[2].1, Token::Asterisk);
    assert_eq!(tokens[12].1, Token::Float(-12.5));
    assert_eq!(tokens[17].1, Token::Text("string".to_owned()));
    assert_eq!(tokens[19].1, Token::Integer(-10));
    assert_eq!(tokens[21].1, Token::Integer(5));
}

#[test]
fn unknown_token() {
    let lex = Lexer::new(lex_rules![
        "test" => |_, _, _| Unknown("test".to_owned())
    ], |_, text| Unknown(text.to_owned()));

    let tokens = lex.src_iter(r#"|"#).collect::<Vec<_>>();

    assert_eq!(tokens[0], Token::Unknown(String::from("|")));
}
