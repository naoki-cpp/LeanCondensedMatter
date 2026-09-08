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
  simp [add_assoc]

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

@[simp] private theorem pauliX_mul_inPlane_zero_zero (x y : ℂ) :
    (pauliX * (x • pauliX + y • pauliY)) 0 0 = x + y * Complex.I := by
  simp [Matrix.mul_apply, pauliX, pauliY]

@[simp] private theorem pauliX_mul_inPlane_one_one (x y : ℂ) :
    (pauliX * (x • pauliX + y • pauliY)) 1 1 = x - y * Complex.I := by
  simp [Matrix.mul_apply, pauliX, pauliY, sub_eq_add_neg]

/-- The ordinary bilinear dot product on Pauli coefficients is the sum of the three semantic
components. No complex conjugation is introduced. -/
@[simp] theorem dotProduct_pauliAxis (u v : PauliAxis → ℂ) :
    dotProduct u v = u .x * v .x + u .y * v .y + u .z * v .z := by
  simp [dotProduct, sum_pauliAxis]

/-- Pauli synthesis commutes with scalar multiplication of the indexed coefficient family. -/
@[simp] theorem pauliCombination_smul (c : ℂ) (u : PauliAxis → ℂ) :
    pauliCombination (c • u) = c • pauliCombination u := by
  simp [pauliCombination, smul_add, smul_smul]
  module

/-- The identity on a two-dimensional internal space has trace two. -/
@[simp] theorem trace_one_pauliMatrix : Matrix.trace (1 : PauliMatrix) = 2 := by
  simp [Matrix.trace]

/-- Every Pauli synthesis is traceless. -/
@[simp] theorem trace_pauliCombination (u : PauliAxis → ℂ) :
    Matrix.trace (pauliCombination u) = 0 := by
  simp [Matrix.trace, pauliCombination, pauliX, pauliY, pauliZ]

/-- The trace pairing of two Pauli syntheses is twice the ordinary bilinear dot product. -/
theorem trace_pauliCombination_mul_pauliCombination (u v : PauliAxis → ℂ) :
    Matrix.trace (pauliCombination u * pauliCombination v) =
      2 * dotProduct u v := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  simp [Matrix.trace, pauliCombination, Matrix.mul_apply, pauliX, pauliY, pauliZ,
    dotProduct, sum_pauliAxis]
  ring_nf
  simp [hI]

/-- Trace overlap of two normalized two-level projector forms `(I + u·σ)/2` and
`(I + v·σ)/2`. -/
theorem trace_halfIdentity_add_pauliCombination_mul_halfIdentity_add_pauliCombination
    (u v : PauliAxis → ℂ) :
    Matrix.trace
        (((1 / 2 : ℂ) • ((1 : PauliMatrix) + pauliCombination u)) *
          ((1 / 2 : ℂ) • ((1 : PauliMatrix) + pauliCombination v))) =
      (1 + dotProduct u v) / 2 := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [add_mul, one_mul, mul_add, mul_one]
  simp [trace_pauliCombination_mul_pauliCombination]
  ring

/-- The square of a Pauli synthesis is its bilinear coefficient square times the identity. -/
theorem pauliCombination_mul_self (u : PauliAxis → ℂ) :
    pauliCombination u * pauliCombination u =
      dotProduct u u • (1 : PauliMatrix) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCombination, Matrix.mul_apply, pauliX, pauliY, pauliZ,
      dotProduct, sum_pauliAxis] <;>
    ring_nf <;>
    simp [hI]

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
