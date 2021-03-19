/*

Prints solution of `x^2 = 16`.

*/

use path_iter::*;

fn main() {
    for a in path!([Square] 16) {
        println!("{:?}", a);
    }
}
