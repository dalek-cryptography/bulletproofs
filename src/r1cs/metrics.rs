/// A struct that contains metrics about a constraint system.
///
/// See [`ConstraintSystem::metrics`](::r1cs::ConstraintSystem::metrics).
#[derive(Debug, Clone)]
pub struct Metrics {
    /// Number of multiplicative constraints in the constraint system.
    pub multipliers: usize,
    /// Total number of linear constraints in the constraint system.
    pub constraints: usize,
    /// Number of linear constraints added in pre-randomization phase.
    pub phase_one_constraints: usize,
    /// Number of linear constraints added in the randomization phase.
    pub phase_two_constraints: usize,
}
