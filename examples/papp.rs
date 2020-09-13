/*

# Partial application example

When `And(x)` is used inside the `path!` macro,
The method `And.papp(x)` is called.

*/

use path_iter::*;

fn main() {
    for a in path!([And(true)] true) {
        println!("{:?}", a);
    }
}
