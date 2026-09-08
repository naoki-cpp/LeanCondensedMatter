import Mathlib.Data.Fintype.Basic

set_option linter.style.header false

/-!
# Pauli coefficient axes

This file owns the model-independent indexing used for three-component Pauli coefficients in
concrete one-particle quantum mechanics. A Pauli coefficient vector is represented directly as a
function `PauliAxis → α`; no parallel vector wrapper is introduced.
-/

namespace QuantumMechanics
namespace SingleParticle

/-- Cartesian axes of a three-component Pauli coefficient vector. -/
inductive PauliAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype

/-- The Pauli coefficient vector with Cartesian components `(x,y,z)`. -/
def pauliCoefficients {α : Type*} (x y z : α) : PauliAxis → α
  | .x => x
  | .y => y
  | .z => z

end SingleParticle
end QuantumMechanics
