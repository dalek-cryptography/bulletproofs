use curve25519_dalek::scalar::Scalar;

use super::Variable;
use super::assignment::Assignment;

/// `OpenWire` allows inspecting its secret assignment because it is guaranteed to be
/// determined and not affected by the challenge value.
/// Open wires are only available in the first phase of building constraint system
/// (before they are committed).
pub struct OpenWire {
    wire: Wire
}

/// `Wire` implements a "closed" wire, that may not have a determined assignment due
/// to the use of challenges to calculate it.
/// Any `OpenWire` can be upcast to `Wire`, so it can be used with gadgets that do not
/// require inspection of the assignments.
/// Note: internally, the assignment is always calculated, even when based on a random challenge,
/// but it is only done after all open wires are committed.
pub struct Wire {
    pub variable: Variable,
    assignment: Assignment,
}

impl OpenWire {
    /// Upcasts to the `Wire`.
    pub fn as_wire(&self) -> &Wire {
        &self.wire
    }

    /// Returns the assignment of the wire.
    pub fn assignment(&self) -> &Assignment {
        &self.wire.assignment
    }
}

/// Wrapped scalar that does not expose its value.
/// When CS samples a random challenge scalar, it is wrapped in `OpaqueScalar`
/// to prevent accidental use of it for making decisions on the prover side.
pub struct OpaqueScalar {
    scalar: Scalar
}


