use curve25519_dalek::scalar::Scalar;

pub fn batch_invert(inputs: &mut [Scalar]) {
    // First, compute the product of all inputs using a product
    // tree:
    //
    // Inputs: [x_0, x_1, x_2]
    //
    // Tree:
    //
    //                 x_0*x_1*x_2*1         tree[1]
    //                   /       \
    //               x_0*x_1     x_2*1       tree[2,3]
    //                / \        / \
    //              x_0  x_1   x_2  1        tree[4,5,6,7]
    //
    //  The leaves of the tree are the inputs.  We store the tree in
    //  an array of length 2*n, similar to a binary heap.
    //
    //  To initialize the tree, set every node to 1, then fill in
    //  the leaf nodes with the input variables.  Finally, set every
    //  non-leaf node to be the product of its children.
    let n = inputs.len().next_power_of_two();
    let mut tree = vec![Scalar::one(); 2*n];
    tree[n..n+inputs.len()].copy_from_slice(inputs);
    for i in (1..n).rev() {
        tree[i] = &tree[2*i] * &tree[2*i+1];
    }

    // The root of the tree is the product of all inputs, and is
    // stored at index 1.  Compute its inverse.
    let allinv = tree[1].invert();

    // To compute y_i = 1/x_i, start at the i-th leaf node of the
    // tree, and walk up to the root of the tree, multiplying
    // `allinv` by each sibling.  This computes
    //
    // y_i = y * (all x_j except x_i)
    //
    // using lg(n) multiplications for each y_i, taking n*lg(n) in
    // total.
    for i in 0..inputs.len() {
        let mut inv = allinv;
        let mut node = n + i;
        while node > 1 {
            inv *= &tree[node ^ 1];
            node = node >> 1;
        }
        inputs[i] = inv;
    }
}

#[cfg(test)]
mod test {
	use super::*;

#[test]
	fn batch_invert_matches_nonbatched() {
		let W = Scalar::from_bits(b"\x84\xfc\xbcOx\x12\xa0\x06\xd7\x91\xd9z:'\xdd\x1e!CE\xf7\xb1\xb9Vz\x810sD\x96\x85\xb5\x07");
		let X = Scalar::from_bits(b"NZ\xb44]G\x08\x84Y\x13\xb4d\x1b\xc2}RR\xa5\x85\x10\x1b\xccBD\xd4I\xf4\xa8y\xd9\xf2\x04");
		let Y = Scalar::from_bits(b"\x90v3\xfe\x1cKf\xa4\xa2\x8d-\xd7g\x83\x86\xc3S\xd0\xdeTU\xd4\xfc\x9d\xe8\xefz\xc3\x1f5\xbb\x05");
		let Z = Scalar::from_bits(b"\x05\x9d>\x0b\t&P=\xa3\x84\xa1<\x92z\xc2\x06A\x98\xcf4:$\xd5\xb7\xeb3j-\xfc\x11!\x0b");

		let list = vec![W, X, Y, Z, W*Y, X*Z, Y*Y, W*Z];
		let mut inv_list = list.clone();
		batch_invert(&mut inv_list[..]);
		for i in 0..8 {
			assert_eq!(list[i].invert(), inv_list[i]);
		}
	}
}
