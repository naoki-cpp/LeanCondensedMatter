import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.CrossProduct
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

/-- Select one semantic Pauli-axis component from explicit `x`, `y`, and `z` values. -/
def pauliAxisComponent {α : Type*} (axis : PauliAxis) (x y z : α) : α :=
  match axis with
  | .x => x
  | .y => y
  | .z => z

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

/-- The Pauli matrix associated with a semantic axis. -/
def pauliBasis : PauliAxis → PauliMatrix
  | .x => pauliX
  | .y => pauliY
  | .z => pauliZ

/-- Every matrix in the Pauli basis is Hermitian. -/
theorem pauliBasis_isHermitian (axis : PauliAxis) :
    (pauliBasis axis).IsHermitian := by
  cases axis <;>
    apply Matrix.IsHermitian.ext <;>
    intro i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [pauliBasis, pauliX, pauliY, pauliZ]

/-- Bilinear Pauli synthesis `u · σ`. The coefficient family is kept as the canonical indexed
function rather than wrapped in a parallel vector type. -/
def pauliCombination (u : PauliAxis → ℂ) : PauliMatrix :=
  ∑ axis : PauliAxis, u axis • pauliBasis axis

/-- Coordinate expansion of the canonical axis-indexed Pauli synthesis. Use this only when a
consumer genuinely needs explicit x/y/z components. -/
theorem pauliCombination_eq_components (u : PauliAxis → ℂ) :
    pauliCombination u =
      u .x • pauliX + u .y • pauliY + u .z • pauliZ := by
  simp [pauliCombination, sum_pauliAxis, pauliBasis]

/-- A Pauli synthesis with real axis coefficients is Hermitian. -/
theorem pauliCombination_ofReal_isHermitian (u : PauliAxis → ℝ) :
    (pauliCombination (fun axis => (u axis : ℂ))).IsHermitian := by
  have hself (r : ℝ) : IsSelfAdjoint ((r : ℂ)) := by
    simp [isSelfAdjoint_iff]
  simpa [pauliCombination, sum_pauliAxis] using
    (((pauliBasis_isHermitian .x).smul (hself (u .x))).add
      ((pauliBasis_isHermitian .y).smul (hself (u .y)))).add
      ((pauliBasis_isHermitian .z).smul (hself (u .z)))

/-- Ordinary bilinear cross product on semantic Pauli-axis coefficient families, obtained by
transporting Mathlib's three-dimensional cross product to the semantic axes. -/
def pauliCross (u v : PauliAxis → ℂ) : PauliAxis → ℂ :=
  let w : Fin 3 → ℂ :=
    crossProduct ![u .x, u .y, u .z] ![v .x, v .y, v .z]
  fun axis => pauliAxisComponent axis (w 0) (w 1) (w 2)

/-- The ordinary bilinear dot product on Pauli coefficients is the sum of the three semantic
components. No complex conjugation is introduced. -/
@[simp] theorem dotProduct_pauliAxis (u v : PauliAxis → ℂ) :
    dotProduct u v = u .x * v .x + u .y * v .y + u .z * v .z := by
  simp [dotProduct, sum_pauliAxis]

private def pauliBasisCoeff (axis : PauliAxis) : PauliAxis → ℂ :=
  fun other => if other = axis then 1 else 0

private theorem pauliCombination_pauliBasisCoeff (axis : PauliAxis) :
    pauliCombination (pauliBasisCoeff axis) = pauliBasis axis := by
  cases axis <;>
    simp [pauliCombination, pauliBasisCoeff, pauliBasis]

private theorem pauliBasis_mul_pauliBasis (a b : PauliAxis) :
    pauliBasis a * pauliBasis b =
      dotProduct (pauliBasisCoeff a) (pauliBasisCoeff b) • (1 : PauliMatrix) +
        Complex.I •
          (pauliCross (pauliBasisCoeff a) (pauliBasisCoeff b) .x • pauliBasis .x +
            pauliCross (pauliBasisCoeff a) (pauliBasisCoeff b) .y • pauliBasis .y +
            pauliCross (pauliBasisCoeff a) (pauliBasisCoeff b) .z • pauliBasis .z) := by
  cases a <;> cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliBasis, pauliBasisCoeff, pauliCross, cross_apply, pauliAxisComponent,
      Matrix.mul_apply, Fin.sum_univ_two, pauliX, pauliY, pauliZ, dotProduct_pauliAxis,
      Complex.I_mul_I]

/-- Pauli synthesis commutes with addition of indexed coefficient families. -/
@[simp] theorem pauliCombination_add (u v : PauliAxis → ℂ) :
    pauliCombination (u + v) = pauliCombination u + pauliCombination v := by
  simp [pauliCombination, sum_pauliAxis, add_smul]
  module

/-- Pauli synthesis commutes with scalar multiplication of the indexed coefficient family. -/
@[simp] theorem pauliCombination_smul (c : ℂ) (u : PauliAxis → ℂ) :
    pauliCombination (c • u) = c • pauliCombination u := by
  simp [pauliCombination, sum_pauliAxis, smul_add, smul_smul]

/-- Product of two synthesized Pauli vectors:
`(u·σ)(v·σ) = (u·v) I + i (u×v)·σ`. -/
theorem pauliCombination_mul_pauliCombination (u v : PauliAxis → ℂ) :
    pauliCombination u * pauliCombination v =
      dotProduct u v • (1 : PauliMatrix) +
        Complex.I • pauliCombination (pauliCross u v) := by
  simp only [pauliCombination, sum_pauliAxis]
  simp [add_mul, mul_add, pauliBasis_mul_pauliBasis, pauliBasisCoeff, pauliCross,
    cross_apply, pauliAxisComponent, dotProduct_pauliAxis]
  module

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

/-- Every matrix in the Pauli basis is traceless. -/
@[simp] theorem trace_pauliBasis (axis : PauliAxis) :
    Matrix.trace (pauliBasis axis) = 0 := by
  cases axis <;>
    simp [Matrix.trace, pauliBasis, pauliX, pauliY, pauliZ]

/-- Every Pauli synthesis is traceless. -/
@[simp] theorem trace_pauliCombination (u : PauliAxis → ℂ) :
    Matrix.trace (pauliCombination u) = 0 := by
  simp [pauliCombination]

/-- The trace pairing of two Pauli syntheses is twice the ordinary bilinear dot product. -/
theorem trace_pauliCombination_mul_pauliCombination (u v : PauliAxis → ℂ) :
    Matrix.trace (pauliCombination u * pauliCombination v) =
      2 * dotProduct u v := by
  rw [pauliCombination_mul_pauliCombination]
  simp
  ring

/-- Tracing one Pauli basis matrix against a synthesized Pauli vector selects that coefficient. -/
theorem trace_pauliBasis_mul_pauliCombination (axis : PauliAxis) (u : PauliAxis → ℂ) :
    Matrix.trace (pauliBasis axis * pauliCombination u) = 2 * u axis := by
  rw [← pauliCombination_pauliBasisCoeff axis,
    trace_pauliCombination_mul_pauliCombination]
  cases axis <;>
    simp [pauliBasisCoeff, dotProduct_pauliAxis]

/-- Tracing a synthesized Pauli vector against one basis matrix selects that coefficient. -/
theorem trace_pauliCombination_mul_pauliBasis (u : PauliAxis → ℂ) (axis : PauliAxis) :
    Matrix.trace (pauliCombination u * pauliBasis axis) = 2 * u axis := by
  rw [Matrix.trace_mul_comm]
  exact trace_pauliBasis_mul_pauliCombination axis u

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
  simp [Matrix.trace, Matrix.mul_apply, pauliCombination_eq_components,
    pauliX, pauliY, pauliZ, sub_eq_add_neg]
  ring_nf
  simp [hI]

/-- The square of a Pauli synthesis is its bilinear coefficient square times the identity. -/
theorem pauliCombination_mul_self (u : PauliAxis → ℂ) :
    pauliCombination u * pauliCombination u =
      dotProduct u u • (1 : PauliMatrix) := by
  rw [pauliCombination_mul_pauliCombination]
  have hcross : pauliCross u u = 0 := by
    funext axis
    cases axis <;> simp [pauliCross, pauliAxisComponent]
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

/-- A coordinate Pauli shift `a I - (x σₓ + y σᵧ + z σ_z)` has the inverse-scaled companion as a
right inverse whenever its quadratic denominator is nonzero. -/
theorem pauliShiftMatrix_mul_closedInverse
    (a x y z : ℂ) (hden : a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 ≠ 0) :
    (a • (1 : PauliMatrix) - (x • pauliX + y • pauliY + z • pauliZ)) *
      ((a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2)⁻¹ •
        (a • (1 : PauliMatrix) + (x • pauliX + y • pauliY + z • pauliZ))) = 1 := by
  let u : PauliAxis → ℂ
    | .x => x
    | .y => y
    | .z => z
  have hcombination :
      pauliCombination u = x • pauliX + y • pauliY + z • pauliZ := by
    simp [pauliCombination_eq_components, u]
  have hdot : dotProduct u u = x ^ 2 + y ^ 2 + z ^ 2 := by
    rw [dotProduct_pauliAxis]
    simp [u, pow_two]
  have hquadratic := pauliShift_mul_companion a u
  rw [hcombination, hdot] at hquadratic
  have hdenEq :
      a ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) = a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
    ring
  rw [hdenEq] at hquadratic
  rw [mul_smul_comm, hquadratic, smul_smul]
  simp [hden]

end InternalSpace
