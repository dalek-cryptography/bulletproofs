#![allow(non_snake_case)]

use std::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::scalar::Scalar;
use range_proof::inner_product;
use range_proof::commit; // replace with the random oracle

pub struct Prover {

}

pub struct Proof {
	// g_vec: Vec<RistrettoPoint>,
	// h_vec: Vec<RistrettoPoint>,
	// u: RistrettoPoint,
	// p: RistrettoPoint,

	l_vec: Vec<RistrettoPoint>,
	r_vec: Vec<RistrettoPoint>,
	a_final: Scalar,
	b_final: Scalar,
}

impl Prover {
	pub fn prove(
		mut G_vec: Vec<RistrettoPoint>,
		mut H_vec: Vec<RistrettoPoint>,
		Q: RistrettoPoint,
		mut P: RistrettoPoint,
		mut a_vec: Vec<Scalar>,
		mut b_vec: Vec<Scalar>,		
	) -> Proof {
		let G = &mut G_vec[..];
		let H = &mut H_vec[..];
		let a = &mut a_vec[..];
		let b = &mut b_vec[..];

		let mut n = G.len();
		let lg_n = n.next_power_of_two().trailing_zeros() as usize;
		let mut L_vec = Vec::with_capacity(lg_n);
		let mut R_vec = Vec::with_capacity(lg_n);

		while n != 1 {	
			n = n/2;
			let (a_l, a_r) = a.split_at_mut(n);
			let (b_l, b_r) = b.split_at_mut(n);

			let (G_l, G_r) = G.split_at_mut(n);
			let (H_l, H_r) = H.split_at_mut(n);

			let c_l = inner_product(&a_l, &b_r);
			let c_r = inner_product(&a_r, &b_l);

			let L = ristretto::multiscalar_mult(
				a_l.iter().chain(b_r.iter()).chain(iter::once(&c_l)), 
				G_r.iter().chain(H_l.iter()).chain(iter::once(&Q))
			);

			let R = ristretto::multiscalar_mult( 
				a_r.iter().chain(b_l.iter()).chain(iter::once(&c_r)),
				G_l.iter().chain(H_r.iter()).chain(iter::once(&Q))
			);

			L_vec.push(L);
			R_vec.push(R); 

			// TODO: use random oracle for the challenge instead
			let (x, _) = commit(&L, &R);
			let x_inv = x.invert();

			for i in 0..n {
				a_l[i] = a_l[i] * x + a_r[i] * x_inv;
				b_l[i] = b_l[i] * x_inv + b_r[i] * x;
				G_l[i] = ristretto::multiscalar_mult(&[x_inv, x], &[G_l[i], G_r[i]]);
				H_l[i] = ristretto::multiscalar_mult(&[x, x_inv], &[H_l[i], H_r[i]]);
			}
			P += ristretto::multiscalar_mult(&[x*x, x_inv*x_inv], &[L, R]);
			a = a_l;
			b = b_l;
			G = G_l;
			H = H_l;
		}
		debug_assert_eq!(a.len(), 1);
		return Proof {
			l_vec: L_vec,
			r_vec: R_vec,
			a_final: a[0],
			b_final: b[0],
		}
	}
}