/// A struct that contains metrics about a constraint system.
///
/// See [`ConstraintSystem::metrics`](::r1cs::ConstraintSystem::metrics).
#[derive(Debug, Clone)]
pub struct Metrics {
    pub multipliers: usize,
    pub constraints: usize,
    pub phase_one_constraints: usize,
    pub phase_two_constraints: usize,
}
