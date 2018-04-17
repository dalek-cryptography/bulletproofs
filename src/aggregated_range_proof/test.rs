#[cfg(test)]
mod tests {
    use super::*;
    use rand::OsRng;

    fn test_u32(m: usize) {
        let mut rng = OsRng::new().unwrap();
        let v: Vec<u64> = iter::repeat(())
            .map(|()| rng.next_u32() as u64).take(m).collect();
        let rp = Proof::create_multi(v, 32, &mut rng);
        assert!(rp.verify(&mut rng).is_ok());
    }

    fn test_u64(m: usize) {
        let mut rng = OsRng::new().unwrap();
        let v: Vec<u64> = iter::repeat(())
            .map(|()| rng.next_u64()).take(m).collect();
        let rp = Proof::create_multi(v, 64, &mut rng);
        assert!(rp.verify(&mut rng).is_ok());
    }

    #[test]
    fn one_value() {
        test_u32(1);
        test_u64(1);
    }

    #[test]
    fn two_values() {
        test_u32(2);
        test_u64(2);
    }

    #[test]
    fn four_values() {
        test_u32(4);
        test_u64(4);
    }

    #[test]
    fn eight_values() {
        test_u32(8);
        test_u64(8);
    }
}
