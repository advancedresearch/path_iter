use path_iter::*;

fn main() {
    for a in path!([((And, And), (And, And)), (And, And), And] true) {
        println!("{:?}", a);
    }
}
