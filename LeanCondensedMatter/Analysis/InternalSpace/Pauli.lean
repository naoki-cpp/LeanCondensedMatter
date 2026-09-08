import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pauli matrices on a two-dimensional internal space

This module owns the model-independent `2 × 2` complex Pauli matrices and their axis-indexed
bilinear algebra for internal two-level degrees of freedom. Physical interpretations such as spin
or pseudospin belong to downstream models.
-/

namespace InternalSpace

/-- Complex `2 × 2` matrices acting on a two-dimensional internal space. -/
abbrev PauliMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Axes of the model-independent Pauli basis. -/
inductive PauliAxis where
  | x
  | y
  | z
  deriving DecidableEq

instance : Fintype PauliAxis where
  elems := {.x, .y, .z}
  complete := by
    intro axis
    cases axis <;> simp

private theorem sum_pauliAxis {M : Type*} [AddCommMonoid M] (f : PauliAxis → M) :
    ∑ axis : PauliAxis, f axis = f .x + f .y + f .z := by
  change ∑ axis ∈ ({.x, .y, .z} : Finset PauliAxis), f axis = _
  simp

/-- Pauli matrix `σₓ`. -/
def pauliX : PauliMatrix :=
  !![0, 1; 1, 0]

/-- Pauli matrix `σᵧ`. -/
def pauliY : PauliMatrix :=
  !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix `σ_z`. -/
def pauliZ : PauliMatrix :=
  !![1, 0; 0, -1]

/-- Bilinear Pauli synthesis `u · σ`. The coefficient family is kept as the canonical indexed
function rather than wrapped in a parallel vector type. -/
def pauliCombination (u : PauliAxis → ℂ) : PauliMatrix :=
  u .x • pauliX + u .y • pauliY + u .z • pauliZ

@[simp] theorem pauliX_zero_zero : pauliX 0 0 = 0 := rfl
@[simp] theorem pauliX_zero_one : pauliX 0 1 = 1 := rfl
@[simp] theorem pauliX_one_zero : pauliX 1 0 = 1 := rfl
@[simp] theorem pauliX_one_one : pauliX 1 1 = 0 := rfl

@[simp] theorem pauliY_zero_zero : pauliY 0 0 = 0 := rfl
@[simp] theorem pauliY_zero_one : pauliY 0 1 = -Complex.I := rfl
@[simp] theorem pauliY_one_zero : pauliY 1 0 = Complex.I := rfl
@[simp] theorem pauliY_one_one : pauliY 1 1 = 0 := rfl

@[simp] theorem pauliZ_zero_zero : pauliZ 0 0 = 1 := rfl
@[simp] theorem pauliZ_zero_one : pauliZ 0 1 = 0 := rfl
@[simp] theorem pauliZ_one_zero : pauliZ 1 0 = 0 := rfl
@[simp] theorem pauliZ_one_one : pauliZ 1 1 = -1 := rfl

/-- The ordinary bilinear dot product on Pauli coefficients is the sum of the three semantic
components. No complex conjugation is introduced. -/
@[simp] theorem dotProduct_pauliAxis (u v : PauliAxis → ℂ) :
    dotProduct u v = u .x * v .x + u .y * v .y + u .z * v .z := by
  simp [dotProduct, sum_pauliAxis]

/-- The square of a Pauli synthesis is its bilinear coefficient square times the identity. -/
theorem pauliCombination_mul_self (u : PauliAxis → ℂ) :
    pauliCombination u * pauliCombination u =
      dotProduct u u • (1 : PauliMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCombination, Matrix.mul_apply, pauliX, pauliY, pauliZ,
      dotProduct, sum_pauliAxis, Complex.I_mul_I] <;>
    ring

/-- Multiplying opposite-sign Pauli shifts eliminates the Pauli part and leaves the quadratic
bilinear invariant. -/
theorem pauliShift_mul_companion (a : ℂ) (u : PauliAxis → ℂ) :
    (a • (1 : PauliMatrix) - pauliCombination u) *
        (a • (1 : PauliMatrix) + pauliCombination u) =
      (a ^ 2 - dotProduct u u) • (1 : PauliMatrix) := by
  rw [sub_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [pauliCombination_mul_self, pow_two]
  module

end InternalSpace
