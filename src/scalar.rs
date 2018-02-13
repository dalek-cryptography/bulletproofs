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
		let W = Scalar::from_bits(
			[
	            0x84, 0xfc, 0xbc, 0x4f, 0x78, 0x12, 0xa0, 0x06,
	            0xd7, 0x91, 0xd9, 0x7a, 0x3a, 0x27, 0xdd, 0x1e,
	            0x21, 0x43, 0x45, 0xf7, 0xb1, 0xb9, 0x56, 0x7a,
	            0x81, 0x30, 0x73, 0x44, 0x96, 0x85, 0xb5, 0x07,
       		]
		);
		let X = Scalar::from_bits(
	        [
	            0x4e, 0x5a, 0xb4, 0x34, 0x5d, 0x47, 0x08, 0x84,
	            0x59, 0x13, 0xb4, 0x64, 0x1b, 0xc2, 0x7d, 0x52,
	            0x52, 0xa5, 0x85, 0x10, 0x1b, 0xcc, 0x42, 0x44,
	            0xd4, 0x49, 0xf4, 0xa8, 0x79, 0xd9, 0xf2, 0x04,
	        ]
		);
		let Y = Scalar::from_bits(
	        [
	            0x90, 0x76, 0x33, 0xfe, 0x1c, 0x4b, 0x66, 0xa4,
	            0xa2, 0x8d, 0x2d, 0xd7, 0x67, 0x83, 0x86, 0xc3,
	            0x53, 0xd0, 0xde, 0x54, 0x55, 0xd4, 0xfc, 0x9d,
	            0xe8, 0xef, 0x7a, 0xc3, 0x1f, 0x35, 0xbb, 0x05,
	        ]
		);
		let Z = Scalar::from_bits(
	        [
	            0x05, 0x9d, 0x3e, 0x0b, 0x09, 0x26, 0x50, 0x3d,
	            0xa3, 0x84, 0xa1, 0x3c, 0x92, 0x7a, 0xc2, 0x06,
	            0x41, 0x98, 0xcf, 0x34, 0x3a, 0x24, 0xd5, 0xb7,
	            0xeb, 0x33, 0x6a, 0x2d, 0xfc, 0x11, 0x21, 0x0b,
	        ]
		);

		let list = vec![W, X, Y, Z, W*Y, X*Z, Y*Y, W*Z];
		let mut inv_list = list.clone();
		batch_invert(&mut inv_list[..]);
		for i in 0..8 {
			assert_eq!(list[i].invert(), inv_list[i]);
		}
	}
}