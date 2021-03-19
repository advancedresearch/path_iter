/*

Prints all solutions of `a + b = 42` where `a` and `b` are positive.

*/

use path_iter::*;

fn main() {
    let x = 42;
    for a in path!([Add] x) {
        if a.0 > 0 && a.1 > 0 {
            println!("{:?}", a);
        } else if a.1 == x {
            break;
        }
    }
}
