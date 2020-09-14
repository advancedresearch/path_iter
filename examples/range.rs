use path_iter::*;

fn main() {
    for a in path!([Neg] 0..10) {
        println!("{:?}", a);
    }
}
