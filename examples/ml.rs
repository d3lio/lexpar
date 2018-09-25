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
    if a == 1 then
        c a
    else if b == 1 then
        c b
    else
        c 1

if a then
    if b then
        c
    else
        a

if _a then
    if _b then
        _c
else
    _a

if a1 then if b1 then c1 else a1

// if a1 then if b1 then c1
// else
//     a1

f ((x)) (id 1) z 1.1 -5 c

let a = ||
    print 123

fn fib n =
    let a = 0
    let b = 1
    if n == 0 or n == 1 then
        n
    else for i in 2..n do
        let t = a + b
        a = b
        b = t

    // if a1 then if b1 then c1
    // else
    //     a1

    b

let s = ""

let str = "fin\"ally"
"#;

fn main() {
    ml_family::run(SRC);
}
