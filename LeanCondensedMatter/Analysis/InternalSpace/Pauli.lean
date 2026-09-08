import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

set_option linter.style.header false

/-!
# Pauli matrices on a two-dimensional internal space

This module owns the model-independent `2 × 2` complex Pauli matrices used for internal two-level
degrees of freedom. Physical interpretations such as spin or pseudospin belong to downstream
models.
-/

namespace InternalSpace

/-- Complex `2 × 2` matrices acting on a two-dimensional internal space. -/
abbrev PauliMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrix `σₓ`. -/
def pauliX : PauliMatrix :=
  !![0, 1; 1, 0]

/-- Pauli matrix `σᵧ`. -/
def pauliY : PauliMatrix :=
  !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix `σ_z`. -/
def pauliZ : PauliMatrix :=
  !![1, 0; 0, -1]

end InternalSpace
