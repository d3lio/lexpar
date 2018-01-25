mod lexer;
mod parser;

pub fn run(source: &str) {
    let lexer = lexer::lexer();
    let iter = lexer.src_iter(source);
    let ast = parser::Parser::parse(iter);

    match ast {
        Ok(exprs) => for expr in exprs { println!("{:?}\n", expr) }
        Err(err)=> println!("{:?}", err)
    }
}
