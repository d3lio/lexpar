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
        r"[ \t\n]+"                 => |text, span| (span, Whitespace(text.to_owned())),
        r"/\*[^(?:*/)]*\*/"         => |text, span| (span, Comment(text[2..text.len() - 2].to_owned())),
        r"//[^\n]*"                 => |text, span| (span, Comment(text[2..].to_owned())),
        Kw::pattern()               => |text, span| (span, Keyword(Kw::from(text))),
        r"[_a-zA-Z][_a-zA-Z0-9]*"   => |text, span| (span, Ident(text.to_owned())),
        r"-?[0-9]+\.[0-9]*"         => |text, span| (span, Float(text.parse().unwrap())),
        r"-?[0-9]+"                 => |text, span| (span, Integer(text.parse().unwrap())),
        r"->"                       => |_, span| (span, Arrow),
        r"="                        => |_, span| (span, Assign),
        r"\("                       => |_, span| (span, LParen),
        r"\)"                       => |_, span| (span, RParen),
        r"\["                       => |_, span| (span, LBracket),
        r"\]"                       => |_, span| (span, RBracket),
        r"\{"                       => |_, span| (span, LBrace),
        r"\}"                       => |_, span| (span, RBrace),
        r"\+"                       => |_, span| (span, Plus),
        r"\-"                       => |_, span| (span, Minus),
        r"\*"                       => |_, span| (span, Asterisk),
        r"/"                        => |_, span| (span, FSlash)
    ], |text, span| (span, Unknown(text.to_owned())));

    let tokens = lex.src_iter(
        r#"
        {*/}[+(he
        _llo)-12.5h3]/*multi
        line
        comment
        */
        -10 5
        //hello fdsf
        //|
        "#).collect::<Vec<_>>();

    assert_eq!(tokens[2].1, Token::Asterisk);
    assert_eq!(tokens[12].1, Token::Float(-12.5));
    assert_eq!(tokens[17].1, Token::Integer(-10));
    assert_eq!(tokens[19].1, Token::Integer(5));
}

#[test]
fn unknown_token() {
    let lex = Lexer::new(lex_rules![
        "test" => |_, _| Unknown("test".to_owned())
    ], |text, _| Unknown(text.to_owned()));

    let tokens = lex.src_iter(r#"|"#).collect::<Vec<_>>();
    println!("{:?}", tokens);

    assert_eq!(tokens[0], Token::Unknown(String::from("|")));
}
