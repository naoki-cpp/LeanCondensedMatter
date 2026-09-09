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

/-- Ordinary bilinear cross product on semantic Pauli-axis coefficient families. -/
def pauliCross (u v : PauliAxis → ℂ) : PauliAxis → ℂ
  | .x => u .y * v .z - u .z * v .y
  | .y => u .z * v .x - u .x * v .z
  | .z => u .x * v .y - u .y * v .x

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

/-- Pauli synthesis commutes with addition of indexed coefficient families. -/
@[simp] theorem pauliCombination_add (u v : PauliAxis → ℂ) :
    pauliCombination (u + v) = pauliCombination u + pauliCombination v := by
  simp [pauliCombination, add_smul]
  module

/-- Pauli synthesis commutes with scalar multiplication of the indexed coefficient family. -/
@[simp] theorem pauliCombination_smul (c : ℂ) (u : PauliAxis → ℂ) :
    pauliCombination (c • u) = c • pauliCombination u := by
  simp [pauliCombination, smul_add, smul_smul]

/-- Product of two synthesized Pauli vectors:
`(u·σ)(v·σ) = (u·v) I + i (u×v)·σ`. -/
theorem pauliCombination_mul_pauliCombination (u v : PauliAxis → ℂ) :
    pauliCombination u * pauliCombination v =
      dotProduct u v • (1 : PauliMatrix) +
        Complex.I • pauliCombination (pauliCross u v) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCombination, pauliCross, Matrix.mul_apply, pauliX, pauliY, pauliZ,
      dotProduct, sum_pauliAxis] <;>
    ring_nf <;>
    simp [hI] <;>
    ring

/-- Product of two scalar-plus-Pauli forms. -/
theorem pauliAffine_mul_pauliAffine (a b : ℂ) (u v : PauliAxis → ℂ) :
    (a • (1 : PauliMatrix) + pauliCombination u) *
        (b • (1 : PauliMatrix) + pauliCombination v) =
      (a * b + dotProduct u v) • (1 : PauliMatrix) +
        pauliCombination (a • v + b • u + Complex.I • pauliCross u v) := by
  rw [add_mul, mul_add, mul_add, pauliCombination_mul_pauliCombination]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [pauliCombination_add, pauliCombination_add,
    pauliCombination_smul, pauliCombination_smul, pauliCombination_smul]
  module

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
  simp [Matrix.trace, pauliCombination, pauliX, pauliY, pauliZ,
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

/-- The `x-y` Pauli trace through opposite two-level halves depends only on the indexed
coefficients: the symmetric part is `-uₓuᵧ` and the antisymmetric part is `-i u_z`.
Scalar vertex factors are included so downstream models do not need to reopen matrix entries. -/
theorem trace_halfIdentity_sub_pauliCombination_mul_scaledPauliX_mul_halfIdentity_add_pauliCombination_mul_scaledPauliY
    (u : PauliAxis → ℂ) (a b : ℂ) :
    Matrix.trace
        (((1 / 2 : ℂ) • ((1 : PauliMatrix) - pauliCombination u)) *
          (a • pauliX) *
          ((1 / 2 : ℂ) • ((1 : PauliMatrix) + pauliCombination u)) *
          (b • pauliY)) =
      a * b * (-(u .x * u .y) - Complex.I * u .z) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  simp [Matrix.trace, Matrix.mul_apply, pauliCombination, pauliX, pauliY, pauliZ,
    sub_eq_add_neg]
  ring_nf
  simp [hI]

/-- The square of a Pauli synthesis is its bilinear coefficient square times the identity. -/
theorem pauliCombination_mul_self (u : PauliAxis → ℂ) :
    pauliCombination u * pauliCombination u =
      dotProduct u u • (1 : PauliMatrix) := by
  rw [pauliCombination_mul_pauliCombination]
  have hcross : pauliCross u u = 0 := by
    funext axis
    cases axis <;> simp [pauliCross] <;> ring
  rw [hcross]
  simp [pauliCombination]

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
