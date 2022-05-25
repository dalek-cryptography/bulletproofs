use blake2::Blake2b;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use digest::Digest;
use sha3::Sha3_512;

/// Defines a `ScalarProtocol` trait for using a Scalar
pub trait ScalarProtocol {
    /// Construct a scalar from an existing Blake2b instance (helper function to implement 'Scalar::from_hash<Blake2b>')
    fn from_hasher_blake2b(hasher: Blake2b) -> Scalar;
}

impl ScalarProtocol for Scalar {
    fn from_hasher_blake2b(hasher: Blake2b) -> Scalar {
        let mut output = [0u8; 64];
        output.copy_from_slice(hasher.finalize().as_slice());
        Scalar::from_bytes_mod_order_wide(&output)
    }
}

// Defines a `RistrettoPointProtocol` trait for using a RistrettoPoint
pub trait RistrettoPointProtocol {
    /// Helper function to implement 'RistrettoPoint::hash_from_bytes::<Sha3_512>'
    fn hash_from_bytes_sha3_512(input: &[u8]) -> RistrettoPoint;

    /// Helper function to implement 'RistrettoPoint::from_hash::<Sha3_512>'
    fn from_hash_sha3_512(hasher: Sha3_512) -> RistrettoPoint;
}

impl RistrettoPointProtocol for RistrettoPoint {
    fn hash_from_bytes_sha3_512(input: &[u8]) -> RistrettoPoint {
        let mut hasher = Sha3_512::default();
        digest::Digest::update(&mut hasher, input);
        Self::from_hash_sha3_512(hasher)
    }

    fn from_hash_sha3_512(hasher: Sha3_512) -> RistrettoPoint {
        let output = hasher.finalize();
        RistrettoPoint::from_uniform_bytes(&output.into())
    }
}
