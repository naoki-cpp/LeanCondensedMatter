import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

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
@[reducible] def pauliX : PauliMatrix :=
  !![0, 1; 1, 0]

/-- Pauli matrix `σᵧ`. -/
@[reducible] def pauliY : PauliMatrix :=
  !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix `σ_z`. -/
@[reducible] def pauliZ : PauliMatrix :=
  !![1, 0; 0, -1]

@[simp] theorem matrix_eq_smul_pauliX (c : ℂ) :
    !![0, c; c, 0] = c • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

@[simp] theorem matrix_eq_smul_pauliY (c : ℂ) :
    !![0, -(c * Complex.I); c * Complex.I, 0] = c • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY]

@[simp] theorem matrix_eq_smul_pauliZ (c : ℂ) :
    !![c, 0; 0, -c] = c • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

end InternalSpace
