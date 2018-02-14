use std::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::traits::Identity;
use curve25519_dalek::scalar::Scalar;
use range_proof::inner_product;
use range_proof::commit; // replace with the random oracle

pub struct Prover {

}

pub struct Proof {
	g_vec: Vec<RistrettoPoint>,
	h_vec: Vec<RistrettoPoint>,
	u: RistrettoPoint,
	p: RistrettoPoint,

	l_vec: Vec<RistrettoPoint>,
	r_vec: Vec<RistrettoPoint>,
	a_final: Scalar,
	b_final: Scalar,
}

impl Prover {
	pub fn prove(
		g_vec: Vec<RistrettoPoint>,
		h_vec: Vec<RistrettoPoint>,
		u: RistrettoPoint,
		p: RistrettoPoint,
		a: Vec<Scalar>,
		b: Vec<Scalar>,		
	) -> Proof {
		let g_prime = g_vec.clone();
		let h_prime = h_vec.clone();
		let p_prime = p.clone();
		let n = g_prime.len(); // change to ln(g.len())
		let l_vec = Vec::with_capacity(n);
		let r_vec = Vec::with_capacity(n);
		let (a_final, b_final) = Prover::recurse(g_prime, h_prime, u, p_prime, &l_vec, &r_vec, a, b);
		Proof {
			g_vec: g_vec,
			h_vec: h_vec,
			u: u,
			p: p,
			l_vec: l_vec,
			r_vec: r_vec,
			a_final: a_final,
			b_final: b_final,
		}
	}

	fn recurse(
		g_vec: Vec<RistrettoPoint>,
		h_vec: Vec<RistrettoPoint>,
		u: RistrettoPoint,
		p: RistrettoPoint,
		l_vec: &Vec<RistrettoPoint>,
		r_vec: &Vec<RistrettoPoint>,
		a: Vec<Scalar>,
		b: Vec<Scalar>,
	) -> (Scalar, Scalar) {
		let mut n = g_vec.len();
		if n == 1 {
			return (a[0], b[0]);
		}
		n = n/2;
		let c_l = inner_product(&a[..n], &b[n..]);
		let c_r = inner_product(&a[n..], &b[..n]);

		let l_points_iter = g_vec[n..].iter().chain(h_vec[..n].iter()).chain(iter::once(&u));
		let l_scalars_iter = a[..n].iter().chain(b[n..].iter()).chain(iter::once(&c_l));
		let big_l = ristretto::multiscalar_mult(l_scalars_iter, l_points_iter);

		let r_points_iter = g_vec[..n].iter().chain(h_vec[n..].iter()).chain(iter::once(&u));
		let r_scalars_iter = a[n..].iter().chain(b[..n].iter()).chain(iter::once(&c_r));
		let big_r = ristretto::multiscalar_mult(r_scalars_iter, r_points_iter);

		// TODO: use random oracle for the challenge instead
		// TODO: store big_l, big_r in l_vec, r_vec
		let (x, _) = commit(&big_l, &big_r);
		(a[0], b[0])
	}
}