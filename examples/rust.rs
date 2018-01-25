#[macro_use]
extern crate lexpar;

mod rust_family;

const SRC: &str = r#"
fn f(a, b, c, d, e, f) {
    g() + 2 * f() + 3
    123
}

fn g() {}
g()

fn main(argv) {
    let a = 1;
    let b = 2;
    let c = fn h() {};
    f()
}

f(((x)), g(), z, 1.1, -5, c)
"#;

fn main() {
    rust_family::run(SRC);
}
