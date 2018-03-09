#![allow(non_snake_case)]

use std::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::scalar::Scalar;

// XXX upstream into dalek
use scalar;

use proof_transcript::RandomOracle;

use range_proof::inner_product;
use range_proof::make_generators;

use sha2::Sha256;

pub struct Proof {
    L_vec: Vec<RistrettoPoint>,
    R_vec: Vec<RistrettoPoint>,
    a: Scalar,
    b: Scalar,
}

impl Proof {
    /// Create an inner-product proof.
    ///
    /// The `verifier` is passed in as a parameter so that the
    /// challenges depend on the *entire* transcript (including parent
    /// protocols).
    pub fn create(
        verifier: &mut RandomOracle,
        P: &RistrettoPoint,
        Q: &RistrettoPoint,
        mut G_vec: Vec<RistrettoPoint>,
        mut H_vec: Vec<RistrettoPoint>,
        mut a_vec: Vec<Scalar>,
        mut b_vec: Vec<Scalar>,
    ) -> Proof {
        // Create slices G, H, a, b backed by their respective
        // vectors.  This lets us reslice as we compress the lengths
        // of the vectors in the main loop below.
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n);
        assert_eq!(H.len(), n);
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);

        let lg_n = n.next_power_of_two().trailing_zeros() as usize;
        let mut L_vec = Vec::with_capacity(lg_n);
        let mut R_vec = Vec::with_capacity(lg_n);

        while n != 1 {
            n = n / 2;
            let (a_L, a_R) = a.split_at_mut(n);
            let (b_L, b_R) = b.split_at_mut(n);
            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            let c_L = inner_product(&a_L, &b_R);
            let c_R = inner_product(&a_R, &b_L);

            let L = ristretto::vartime::multiscalar_mult(
                a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)),
                G_R.iter().chain(H_L.iter()).chain(iter::once(Q)),
            );

            let R = ristretto::vartime::multiscalar_mult(
                a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)),
                G_L.iter().chain(H_R.iter()).chain(iter::once(Q)),
            );

            L_vec.push(L);
            R_vec.push(R);

            verifier.commit(L.compress().as_bytes());
            verifier.commit(R.compress().as_bytes());

            let x = verifier.challenge_scalar();
            let x_inv = x.invert();

            for i in 0..n {
                a_L[i] = a_L[i] * x + x_inv * a_R[i];
                b_L[i] = b_L[i] * x_inv + x * b_R[i];
                G_L[i] = ristretto::vartime::multiscalar_mult(&[x_inv, x], &[G_L[i], G_R[i]]);
                H_L[i] = ristretto::vartime::multiscalar_mult(&[x, x_inv], &[H_L[i], H_R[i]]);
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        return Proof {
            L_vec: L_vec,
            R_vec: R_vec,
            a: a[0],
            b: b[0],
        };
    }

    fn verify(
        &self,
        verifier: &mut RandomOracle,
        P: &RistrettoPoint,
        Q: &RistrettoPoint,
        G_vec: &Vec<RistrettoPoint>,
        H_vec: &Vec<RistrettoPoint>,
    ) -> Result<(), ()> {
        // XXX prover should commit to n
        let lg_n = self.L_vec.len();
        let n = 1 << lg_n;

        // XXX figure out how ser/deser works for Proofs
        // maybe avoid this compression
        let mut challenges = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            verifier.commit(L.compress().as_bytes());
            verifier.commit(R.compress().as_bytes());

            challenges.push(verifier.challenge_scalar());
        }

        let mut inv_challenges = challenges.clone();
        let allinv = scalar::batch_invert(&mut inv_challenges);

        for x in challenges.iter_mut() {
            *x = &*x * &*x; // wtf
        }
        let challenges_sq = challenges;

        // j-th bit of i
        let bit = |i, j| 1 & (i >> j);

        let mut s = Vec::with_capacity(n);
        for i in 0..n {
            let mut s_i = allinv;
            for j in 0..lg_n {
                if bit(i, j) == 1 {
                    // The challenges are stored in "creation order" as [x_k,...,x_1]
                    s_i *= challenges_sq[(lg_n - 1) - j];
                }
            }
            s.push(s_i);
        }
        let s = s;

        // so many allocs :(
        // these were supposed to be iterators but the dalek trait doesn't accept values

        let ab = self.a * self.b;

        let a_times_s: Vec<_> = s.iter().map(|s_i| self.a * s_i).collect();

        let b_div_s: Vec<_> = s.iter().rev().map(|s_i_inv| self.b * s_i_inv).collect();

        let neg_x_sq: Vec<_> = challenges_sq.iter().map(|x| -x).collect();

        let neg_x_inv_sq: Vec<_> = inv_challenges
            .iter()
            .map(|x_inv| -(x_inv * x_inv))
            .collect();

        let scalar_iter = iter::once(&ab)
            .chain(a_times_s.iter())
            .chain(b_div_s.iter())
            .chain(neg_x_sq.iter())
            .chain(neg_x_inv_sq.iter());

        let points_iter = iter::once(Q)
            .chain(G_vec.iter())
            .chain(H_vec.iter())
            .chain(self.L_vec.iter())
            .chain(self.R_vec.iter());

        let expect_P = ristretto::vartime::multiscalar_mult(scalar_iter, points_iter);

        if expect_P == *P { Ok(()) } else { Err(()) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_helper_create(n: usize, expected_a: &[u8; 32], expected_b: &[u8; 32]) {
        let mut verifier = RandomOracle::new(b"innerproducttest");
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);

        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        let Q = RistrettoPoint::hash_from_bytes::<Sha256>(b"test point");
        let c = inner_product(&a_vec, &b_vec);

        let P = ristretto::vartime::multiscalar_mult(
            a_vec.iter().chain(b_vec.iter()).chain(iter::once(&c)),
            G_vec.iter().chain(H_vec.iter()).chain(iter::once(&Q)),
        );

        let proof = Proof::create(
            &mut verifier,
            &P,
            &Q,
            G_vec.clone(),
            H_vec.clone(),
            a_vec.clone(),
            b_vec.clone(),
        );

        let mut verifier = RandomOracle::new(b"innerproducttest");
        assert!(proof.verify(&mut verifier, &P, &Q, &G_vec, &H_vec).is_ok());

        //assert_eq!(proof.a.as_bytes(), expected_a);
        //assert_eq!(proof.b.as_bytes(), expected_b);
    }

    #[test]
    fn make_ipp_1() {
        test_helper_create(1, &[0; 32], &[0; 32]);
    }

    #[test]
    fn make_ipp_2() {
        test_helper_create(2, &[0; 32], &[0; 32]);
    }

    #[test]
    fn make_ipp_4() {
        test_helper_create(4, &[0; 32], &[0; 32]);
    }

    #[test]
    fn make_ipp_64() {
        // These test vectors don't have a ground truth, they're just to catch accidental changes to the computation.
        test_helper_create(
            64,
            b"=\xa2\xed\xd2i\x1a\xb3'oF\xba:S\x12.\xbd)\xe1F\xbeI\xb4+\x11V&\xa6\xae\x1fGd\x04",
            b"zD\xdb\xa5\xd34fO\xde\x8ctu\xa6$\\zS\xc2\x8d|\x93hW\"\xacLL]?\x8e\xc8\x08",
        );
    }

    #[test]
    fn make_ipp_32() {
        // These test vectors don't have a ground truth, they're just to catch accidental changes to the computation.
        test_helper_create(
            32,
            b"l\xa3\xa8\xda\xca\xf9\xdbec|i\xb32i\xc0'\xc3H\xde+\xa0P\x0e;.\xf5\x9cf'?\xa6\n",
            b"\xebr[X{\x90\xa5s\xf0[\xdb\xc3\x86\xd8\xa1:\x86\x91\xbcW@\xa1\x1cv\\\xea9\xcdN~L\x05",
        );
    }
}

#[cfg(test)]
mod bench {

    use super::*;
    use test::Bencher;

    fn bench_helper_create(n: usize, b: &mut Bencher) {
        let mut verifier = RandomOracle::new(b"innerproducttest");
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);
        let Q = RistrettoPoint::hash_from_bytes::<Sha256>("more".as_bytes());
        let P = RistrettoPoint::hash_from_bytes::<Sha256>("points".as_bytes());
        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        b.iter(|| {
            Proof::create(
                &mut verifier,
                &P,
                &Q,
                G_vec.clone(),
                H_vec.clone(),
                a_vec.clone(),
                b_vec.clone(),
            )
        });
    }

    fn bench_helper_verify(n: usize, b: &mut Bencher) {
        let mut verifier = RandomOracle::new(b"innerproducttest");
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);

        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        let Q = RistrettoPoint::hash_from_bytes::<Sha256>(b"test point");
        let c = inner_product(&a_vec, &b_vec);

        let P = ristretto::vartime::multiscalar_mult(
            a_vec.iter().chain(b_vec.iter()).chain(iter::once(&c)),
            G_vec.iter().chain(H_vec.iter()).chain(iter::once(&Q)),
        );

        let proof = Proof::create(
            &mut verifier,
            &P,
            &Q,
            G_vec.clone(),
            H_vec.clone(),
            a_vec.clone(),
            b_vec.clone(),
        );

        let mut verifier = RandomOracle::new(b"innerproducttest");
        b.iter(|| proof.verify(&mut verifier, &P, &Q, &G_vec, &H_vec));
    }

    #[bench]
    fn create_n_eq_64(b: &mut Bencher) {
        bench_helper_create(64, b);
    }

    #[bench]
    fn create_n_eq_32(b: &mut Bencher) {
        bench_helper_create(32, b);
    }

    #[bench]
    fn create_n_eq_16(b: &mut Bencher) {
        bench_helper_create(16, b);
    }

    #[bench]
    fn verify_n_eq_64(b: &mut Bencher) {
        bench_helper_verify(64, b);
    }

    #[bench]
    fn verify_n_eq_32(b: &mut Bencher) {
        bench_helper_verify(32, b);
    }

    #[bench]
    fn verify_n_eq_16(b: &mut Bencher) {
        bench_helper_verify(16, b);
    }
}
