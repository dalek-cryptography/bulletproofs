#![allow(non_snake_case)]

use std::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::scalar::Scalar;
use range_proof::inner_product;
use range_proof::commit; // replace with the random oracle
use range_proof::make_generators;
use sha2::Sha256;

pub struct Proof {
    l_vec: Vec<RistrettoPoint>,
    r_vec: Vec<RistrettoPoint>,
    a_final: Scalar,
    b_final: Scalar,
}

impl Proof {
    pub fn create(
        mut G_vec: Vec<RistrettoPoint>,
        mut H_vec: Vec<RistrettoPoint>,
        mut P: RistrettoPoint,
        Q: RistrettoPoint,
        mut a_vec: Vec<Scalar>,
        mut b_vec: Vec<Scalar>,
    ) -> Proof {
        let mut G = &mut G_vec[..];
        let mut H = &mut H_vec[..];
        let mut a = &mut a_vec[..];
        let mut b = &mut b_vec[..];

        let mut n = G.len();
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

            let L = ristretto::multiscalar_mult(
                a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)),
                G_R.iter().chain(H_L.iter()).chain(iter::once(&Q)),
            );

            let R = ristretto::multiscalar_mult(
                a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)),
                G_L.iter().chain(H_R.iter()).chain(iter::once(&Q)),
            );

            L_vec.push(L);
            R_vec.push(R);

            // TODO: use random oracle for the challenge instead
            let (x, _) = commit(&L, &R);
            let x_inv = x.invert();

            for i in 0..n {
                a_L[i] = a_L[i] * x + x_inv * a_R[i];
                b_L[i] = b_L[i] * x_inv + x * b_R[i];
                G_L[i] = ristretto::multiscalar_mult(&[x_inv, x], &[G_L[i], G_R[i]]);
                H_L[i] = ristretto::multiscalar_mult(&[x, x_inv], &[H_L[i], H_R[i]]);
            }

            a = a_L;
            b = b_L;
            G = G_L;
            H = H_L;
        }

        return Proof {
            l_vec: L_vec,
            r_vec: R_vec,
            a_final: a[0],
            b_final: b[0],
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_helper_create(n: usize, expected_a: &[u8; 32], expected_b: &[u8; 32]) {
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);
        let Q = RistrettoPoint::hash_from_bytes::<Sha256>("more".as_bytes());
        let P = RistrettoPoint::hash_from_bytes::<Sha256>("points".as_bytes());
        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        let proof = Proof::create(
            G_vec.clone(),
            H_vec.clone(),
            P,
            Q,
            a_vec.clone(),
            b_vec.clone(),
        );

        assert_eq!(proof.a_final.as_bytes(), expected_a);
        assert_eq!(proof.b_final.as_bytes(), expected_b);
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
                G_vec.clone(),
                H_vec.clone(),
                P,
                Q,
                a_vec.clone(),
                b_vec.clone(),
            )
        });
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
}
