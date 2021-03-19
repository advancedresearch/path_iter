/*

# Non-Primitive Pythagorean Triples

For more information, see https://en.wikipedia.org/wiki/Pythagorean_triple

Prints solution of `a^2 + b^2 = c^2`.

*/

use path_iter::*;

fn main() {
    for c in 0..100_i64 {
        for (a, b) in path!([(Square, Square)] [Add] c.pow(2)) {
            if a > 0 && b > 0 && a <= b {
                println!("{}^2 + {}^2 = {}^2", a, b, c);
            } else if a == 0 {
                break;
            }
        }
    }
}
