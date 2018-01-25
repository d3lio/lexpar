#[macro_use]
extern crate lexpar;

mod ml_family;

const SRC: &str = r#"
fn f a b c d e f =
    a + 2 * (f 1) + 3
    123

fn id x = x
id 1

fn main args =
    let a = 1
    let b = 2
    let c = |x| x
    if a == 1 then c a else c b
    if a == 2 then
        c a
    else if b == 3 then
        b
    else
        c 1

f ((x)) (id 1) z 1.1 -5 c

let g = |x|
    print x
"#;

fn main() {
    ml_family::run(SRC);
}
