use path_iter::*;

fn main() {
    for &b in &[false, true] {
        for a in path!([And] b) {
            println!("{:?}", a);
        }
        println!("");
    }
}
