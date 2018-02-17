#![allow(non_snake_case)]
#![feature(nll)]

use std::iter;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::ristretto;
use curve25519_dalek::scalar::Scalar;
use range_proof::inner_product;
use range_proof::commit; // replace with the random oracle
use range_proof::make_generators;
use sha2::Sha256;
pub struct Prover {}

pub struct Proof {
    l_vec: Vec<RistrettoPoint>,
    r_vec: Vec<RistrettoPoint>,
    a_final: Scalar,
    b_final: Scalar,
}

impl Prover {
    pub fn prove(
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
            let (a_l, a_r) = a.split_at_mut(n);
            let (b_l, b_r) = b.split_at_mut(n);
            let (G_l, G_r) = G.split_at_mut(n);
            let (H_l, H_r) = H.split_at_mut(n);

            let c_l = inner_product(&a_l, &b_r);
            let c_r = inner_product(&a_r, &b_l);

            let L = ristretto::multiscalar_mult(
                a_l.iter().chain(b_r.iter()).chain(iter::once(&c_l)),
                G_r.iter().chain(H_l.iter()).chain(iter::once(&Q)),
            );

            let R = ristretto::multiscalar_mult(
                a_r.iter().chain(b_l.iter()).chain(iter::once(&c_r)),
                G_l.iter().chain(H_r.iter()).chain(iter::once(&Q)),
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

            P += ristretto::multiscalar_mult(&[x * x, x_inv * x_inv], &[L, R]);
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
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn make_ipp_64() {
        let n = 64;
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);
        let Q = RistrettoPoint::hash_from_bytes::<Sha256>("more".as_bytes());
        let P = RistrettoPoint::hash_from_bytes::<Sha256>("points".as_bytes());
        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        let proof = Prover::prove(
            G_vec.clone(),
            H_vec.clone(),
            P,
            Q,
            a_vec.clone(),
            b_vec.clone(),
        );

        assert_eq!(
            proof.a_final.as_bytes(),
            b"=\xa2\xed\xd2i\x1a\xb3'oF\xba:S\x12.\xbd)\xe1F\xbeI\xb4+\x11V&\xa6\xae\x1fGd\x04"
        );
        assert_eq!(
            proof.b_final.as_bytes(),
            b"zD\xdb\xa5\xd34fO\xde\x8ctu\xa6$\\zS\xc2\x8d|\x93hW\"\xacLL]?\x8e\xc8\x08"
        );
    }
    #[test]
    fn make_ipp_32() {
        let n = 32;
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);
        let Q = RistrettoPoint::hash_from_bytes::<Sha256>("more".as_bytes());
        let P = RistrettoPoint::hash_from_bytes::<Sha256>("points".as_bytes());
        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        let proof = Prover::prove(
            G_vec.clone(),
            H_vec.clone(),
            P,
            Q,
            a_vec.clone(),
            b_vec.clone(),
        );

        assert_eq!(
            proof.a_final.as_bytes(),
            b"l\xa3\xa8\xda\xca\xf9\xdbec|i\xb32i\xc0'\xc3H\xde+\xa0P\x0e;.\xf5\x9cf'?\xa6\n"
        );
        assert_eq!(
            proof.b_final.as_bytes(),
            b"\xebr[X{\x90\xa5s\xf0[\xdb\xc3\x86\xd8\xa1:\x86\x91\xbcW@\xa1\x1cv\\\xea9\xcdN~L\x05"
        );
    }
}

#[cfg(test)]
mod bench {

    use super::*;
    use test::Bencher;

    #[bench]
    fn make_ipp_64(b: &mut Bencher) {
        let n = 64;
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);
        let Q = RistrettoPoint::hash_from_bytes::<Sha256>("more".as_bytes());
        let P = RistrettoPoint::hash_from_bytes::<Sha256>("points".as_bytes());
        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        b.iter(|| {
            Prover::prove(
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
    fn make_ipp_32(b: &mut Bencher) {
        let n = 32;
        let G = &RistrettoPoint::hash_from_bytes::<Sha256>("hello".as_bytes());
        let H = &RistrettoPoint::hash_from_bytes::<Sha256>("there".as_bytes());
        let G_vec = make_generators(G, n);
        let H_vec = make_generators(H, n);
        let Q = RistrettoPoint::hash_from_bytes::<Sha256>("more".as_bytes());
        let P = RistrettoPoint::hash_from_bytes::<Sha256>("points".as_bytes());
        let a_vec = vec![Scalar::from_u64(1); n];
        let b_vec = vec![Scalar::from_u64(2); n];

        b.iter(|| {
            Prover::prove(
                G_vec.clone(),
                H_vec.clone(),
                P,
                Q,
                a_vec.clone(),
                b_vec.clone(),
            )
        });
    }
}
