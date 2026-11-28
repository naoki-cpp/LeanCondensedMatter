import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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
  apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
  unfold pauliCombination
  apply isSelfAdjoint_sum
  intro axis _
  exact ((pauliBasis_isHermitian axis).smul (by simp [isSelfAdjoint_iff])).isSelfAdjoint

/-- Ordinary bilinear cross product on semantic Pauli-axis coefficient families, obtained by
transporting Mathlib's three-dimensional cross product to the semantic axes. -/
def pauliCross (u v : PauliAxis → ℂ) : PauliAxis → ℂ :=
  let w : Fin 3 → ℂ :=
    crossProduct ![u .x, u .y, u .z] ![v .x, v .y, v .z]
  fun axis => pauliAxisComponent axis (w 0) (w 1) (w 2)

/-- The ordinary bilinear dot product on Pauli coefficients is the sum of the three semantic
components. No complex conjugation is introduced. -/
theorem dotProduct_pauliAxis (u v : PauliAxis → ℂ) :
    dotProduct u v = u .x * v .x + u .y * v .y + u .z * v .z := by
  simp [dotProduct, sum_pauliAxis]

private theorem pauliBasis_mul_pauliBasis (a b : PauliAxis) :
    pauliBasis a * pauliBasis b =
      dotProduct (Pi.single a 1) (Pi.single b 1) • (1 : PauliMatrix) +
        Complex.I •
          (pauliCross (Pi.single a 1) (Pi.single b 1) .x • pauliBasis .x +
            pauliCross (Pi.single a 1) (Pi.single b 1) .y • pauliBasis .y +
            pauliCross (Pi.single a 1) (Pi.single b 1) .z • pauliBasis .z) := by
  cases a <;> cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliBasis, pauliCross, cross_apply, pauliAxisComponent,
      Matrix.mul_apply, Fin.sum_univ_two, pauliX, pauliY, pauliZ, Complex.I_mul_I]

/-- Pauli synthesis commutes with addition of indexed coefficient families. -/
@[simp] theorem pauliCombination_add (u v : PauliAxis → ℂ) :
    pauliCombination (u + v) = pauliCombination u + pauliCombination v :=
  (Fintype.linearCombination ℂ pauliBasis).map_add u v

/-- Pauli synthesis commutes with scalar multiplication of the indexed coefficient family. -/
@[simp] theorem pauliCombination_smul (c : ℂ) (u : PauliAxis → ℂ) :
    pauliCombination (c • u) = c • pauliCombination u :=
  (Fintype.linearCombination ℂ pauliBasis).map_smul c u

/-- Product of two synthesized Pauli vectors:
`(u·σ)(v·σ) = (u·v) I + i (u×v)·σ`. -/
theorem pauliCombination_mul_pauliCombination (u v : PauliAxis → ℂ) :
    pauliCombination u * pauliCombination v =
      dotProduct u v • (1 : PauliMatrix) +
        Complex.I • pauliCombination (pauliCross u v) := by
  simp only [pauliCombination, sum_pauliAxis]
  simp [add_mul, mul_add, pauliBasis_mul_pauliBasis, pauliCross,
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
  simp only [pauliCombination_add, pauliCombination_smul]
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

/-- A half-sum of the identity and any Pauli synthesis has trace one. -/
theorem trace_half_one_add_pauliCombination (u : PauliAxis → ℂ) :
    Matrix.trace ((1 / 2 : ℂ) • ((1 : PauliMatrix) + pauliCombination u)) = 1 := by
  rw [Matrix.trace_smul, Matrix.trace_add, trace_pauliCombination]
  norm_num [Matrix.trace]

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
  have h : pauliCombination (Pi.single axis (1 : ℂ)) = pauliBasis axis := by
    change Fintype.linearCombination ℂ pauliBasis (Pi.single axis 1) = pauliBasis axis
    rw [Fintype.linearCombination_apply_single, one_smul]
  rw [← h, trace_pauliCombination_mul_pauliCombination]
  simp

/-- The three Pauli matrices form a linearly independent family over `ℂ`. -/
theorem pauliBasis_linearIndependent : LinearIndependent ℂ pauliBasis := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients hzero axis
  change pauliCombination coefficients = 0 at hzero
  have htrace := trace_pauliBasis_mul_pauliCombination axis coefficients
  rw [hzero, mul_zero, Matrix.trace_zero] at htrace
  exact (mul_eq_zero.mp htrace.symm).resolve_left (by norm_num)

/-- Tracing a synthesized Pauli vector against one basis matrix selects that coefficient. -/
theorem trace_pauliCombination_mul_pauliBasis (u : PauliAxis → ℂ) (axis : PauliAxis) :
    Matrix.trace (pauliCombination u * pauliBasis axis) = 2 * u axis := by
  rw [Matrix.trace_mul_comm]
  exact trace_pauliBasis_mul_pauliCombination axis u

/-- Scalar coefficient of a complex two-level matrix in the Pauli-affine basis. -/
noncomputable def pauliScalarCoefficient (M : PauliMatrix) : ℂ :=
  (M 0 0 + M 1 1) / 2

/-- Axis-indexed Pauli coefficient of a complex two-level matrix. -/
noncomputable def pauliVectorCoefficient (M : PauliMatrix) : PauliAxis → ℂ
  | .x => (M 0 1 + M 1 0) / 2
  | .y => Complex.I * (M 0 1 - M 1 0) / 2
  | .z => (M 0 0 - M 1 1) / 2

open MeasureTheory in
/-- Scalar Pauli coefficient extraction commutes with an entrywise interval integral
and a complex prefactor, assuming interval integrability of every matrix entry. -/
theorem pauliScalarCoefficient_prefactor_intervalIntegral
    (kernel : ℝ → PauliMatrix) (prefactor : ℂ) (a b : ℝ)
    (hkernel : ∀ i j, IntervalIntegrable (fun p => kernel p i j) volume a b) :
    pauliScalarCoefficient (fun i j => prefactor * ∫ p in a..b, kernel p i j) =
      prefactor * ∫ p in a..b, pauliScalarCoefficient (kernel p) := by
  simp only [pauliScalarCoefficient]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (hkernel 0 0) (hkernel 1 1)]
  ring

open MeasureTheory in
/-- Each Pauli-vector coefficient commutes with an entrywise interval integral
and a complex prefactor, assuming interval integrability of every matrix entry. -/
theorem pauliVectorCoefficient_prefactor_intervalIntegral
    (axis : PauliAxis) (kernel : ℝ → PauliMatrix) (prefactor : ℂ) (a b : ℝ)
    (hkernel : ∀ i j, IntervalIntegrable (fun p => kernel p i j) volume a b) :
    pauliVectorCoefficient (fun i j => prefactor * ∫ p in a..b, kernel p i j) axis =
      prefactor * ∫ p in a..b, pauliVectorCoefficient (kernel p) axis := by
  cases axis <;> simp only [pauliVectorCoefficient, intervalIntegral.integral_div]
  · rw [intervalIntegral.integral_add (hkernel 0 1) (hkernel 1 0)]
    ring
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hkernel 0 1) (hkernel 1 0)]
    ring
  · rw [intervalIntegral.integral_sub (hkernel 0 0) (hkernel 1 1)]
    ring

/-- Every complex two-level matrix is its scalar Pauli-affine coefficient times the identity plus
the Pauli synthesis of its three axis coefficients. -/
theorem eq_pauliAffine_coefficients (M : PauliMatrix) :
    M =
      pauliScalarCoefficient M • (1 : PauliMatrix) +
        pauliCombination (pauliVectorCoefficient M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliScalarCoefficient, pauliVectorCoefficient, pauliCombination_eq_components,
      pauliX, pauliY, pauliZ]
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

/-- Conjugation by `σ_z` leaves the scalar Pauli coefficient unchanged. -/
@[simp] theorem pauliScalarCoefficient_pauliZ_conjugate (M : PauliMatrix) :
    pauliScalarCoefficient (pauliZ * M * pauliZ) = pauliScalarCoefficient M := by
  simp [pauliScalarCoefficient, pauliZ, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
    Fin.sum_univ_two]

/-- Axis action induced by conjugation with `σ_z`: the in-plane components change sign while the
`z` component is unchanged. -/
def pauliZConjugateVector (u : PauliAxis → ℂ) : PauliAxis → ℂ
  | .x => -u .x
  | .y => -u .y
  | .z => u .z

/-- Conjugation by `σ_z` acts on Pauli coefficients by `(uₓ,uᵧ,u_z) ↦ (-uₓ,-uᵧ,u_z)`. -/
@[simp] theorem pauliVectorCoefficient_pauliZ_conjugate (M : PauliMatrix) :
    pauliVectorCoefficient (pauliZ * M * pauliZ) =
      pauliZConjugateVector (pauliVectorCoefficient M) := by
  funext axis
  cases axis <;> simp [pauliVectorCoefficient, pauliZConjugateVector, pauliZ,
    Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] <;> ring

@[simp] theorem pauliScalarCoefficient_neg (M : PauliMatrix) :
    pauliScalarCoefficient (-M) = -pauliScalarCoefficient M := by
  simp [pauliScalarCoefficient]
  ring

@[simp] theorem pauliVectorCoefficient_neg (M : PauliMatrix) :
    pauliVectorCoefficient (-M) = -pauliVectorCoefficient M := by
  funext axis
  cases axis <;> simp [pauliVectorCoefficient] <;> ring

/-- Trace of two Pauli-affine matrices in scalar/vector coefficient form. -/
theorem trace_pauliAffine_mul_pauliAffine
    (a b : ℂ) (u v : PauliAxis → ℂ) :
    Matrix.trace
        ((a • (1 : PauliMatrix) + pauliCombination u) *
          (b • (1 : PauliMatrix) + pauliCombination v)) =
      2 * (a * b + dotProduct u v) := by
  rw [pauliAffine_mul_pauliAffine, Matrix.trace_add, Matrix.trace_smul,
    trace_pauliCombination]
  simp [Matrix.trace]
  ring

/-- Trace of four Pauli-affine matrices as one scalar expression. Pairing the first two and last
two factors keeps the result compact and exposes only dot and cross products of Pauli coefficients. -/
theorem trace_four_pauliAffine
    (a b c d : ℂ) (u v w x : PauliAxis → ℂ) :
    Matrix.trace
        ((a • (1 : PauliMatrix) + pauliCombination u) *
          (b • (1 : PauliMatrix) + pauliCombination v) *
          (c • (1 : PauliMatrix) + pauliCombination w) *
          (d • (1 : PauliMatrix) + pauliCombination x)) =
      2 *
        ((a * b + dotProduct u v) * (c * d + dotProduct w x) +
          dotProduct
            (a • v + b • u + Complex.I • pauliCross u v)
            (c • x + d • w + Complex.I • pauliCross w x)) := by
  rw [mul_assoc
    ((a • (1 : PauliMatrix) + pauliCombination u) *
      (b • (1 : PauliMatrix) + pauliCombination v))
    (c • (1 : PauliMatrix) + pauliCombination w)
    (d • (1 : PauliMatrix) + pauliCombination x)]
  rw [pauliAffine_mul_pauliAffine, pauliAffine_mul_pauliAffine,
    trace_pauliAffine_mul_pauliAffine]

/-- Antisymmetrizing the first and third Pauli-affine insertions eliminates
all scalar and bilinear (even-Pauli) trace terms. Only oriented Pauli
triple products remain; the dot and cross products are complex bilinear. -/
theorem trace_four_pauliAffine_antisymmetric
    (a b c d : ℂ) (u v w x : PauliAxis → ℂ) :
    Matrix.trace
        ((a • (1 : PauliMatrix) + pauliCombination u) *
          (b • (1 : PauliMatrix) + pauliCombination v) *
          (c • (1 : PauliMatrix) + pauliCombination w) *
          (d • (1 : PauliMatrix) + pauliCombination x)) -
      Matrix.trace
        ((c • (1 : PauliMatrix) + pauliCombination w) *
          (b • (1 : PauliMatrix) + pauliCombination v) *
          (a • (1 : PauliMatrix) + pauliCombination u) *
          (d • (1 : PauliMatrix) + pauliCombination x)) =
      4 * Complex.I *
        (a * dotProduct v (pauliCross w x) +
          b * dotProduct u (pauliCross w x) +
          c * dotProduct (pauliCross u v) x +
          d * dotProduct (pauliCross u v) w) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  rw [trace_four_pauliAffine, trace_four_pauliAffine]
  simp [dotProduct_pauliAxis, pauliCross, cross_apply, pauliAxisComponent,
    smul_eq_mul]
  ring_nf
  simp only [hI]
  ring

/-- The antisymmetric four-factor trace of arbitrary complex two-level
matrices is controlled only by oriented triple products of their canonical
Pauli coefficients. Symmetric terms cancel before specializing any model. -/
theorem trace_four_antisymmetric_eq_pauliCoefficients
    (A B C D : PauliMatrix) :
    Matrix.trace (A * B * C * D) - Matrix.trace (C * B * A * D) =
      4 * Complex.I *
        (pauliScalarCoefficient A *
            dotProduct (pauliVectorCoefficient B)
              (pauliCross (pauliVectorCoefficient C) (pauliVectorCoefficient D)) +
          pauliScalarCoefficient B *
            dotProduct (pauliVectorCoefficient A)
              (pauliCross (pauliVectorCoefficient C) (pauliVectorCoefficient D)) +
          pauliScalarCoefficient C *
            dotProduct
              (pauliCross (pauliVectorCoefficient A) (pauliVectorCoefficient B))
              (pauliVectorCoefficient D) +
          pauliScalarCoefficient D *
            dotProduct
              (pauliCross (pauliVectorCoefficient A) (pauliVectorCoefficient B))
              (pauliVectorCoefficient C)) := by
  simpa only [← eq_pauliAffine_coefficients A,
    ← eq_pauliAffine_coefficients B, ← eq_pauliAffine_coefficients C,
    ← eq_pauliAffine_coefficients D] using
    (trace_four_pauliAffine_antisymmetric
      (pauliScalarCoefficient A) (pauliScalarCoefficient B)
      (pauliScalarCoefficient C) (pauliScalarCoefficient D)
      (pauliVectorCoefficient A) (pauliVectorCoefficient B)
      (pauliVectorCoefficient C) (pauliVectorCoefficient D))

/-- When the second and fourth Pauli vectors lie in the xz plane, the
antisymmetric four-matrix trace reduces to scalar coefficients and oriented
two-by-two minors. No Hermiticity or complex conjugation is assumed. -/
theorem trace_four_antisymmetric_eq_xz_plane_minors
    (A B C D : PauliMatrix)
    (hB : pauliVectorCoefficient B .y = 0)
    (hD : pauliVectorCoefficient D .y = 0) :
    let a := pauliScalarCoefficient A
    let b := pauliScalarCoefficient B
    let c := pauliScalarCoefficient C
    let d := pauliScalarCoefficient D
    let u := pauliVectorCoefficient A
    let v := pauliVectorCoefficient B
    let w := pauliVectorCoefficient C
    let x := pauliVectorCoefficient D
    Matrix.trace (A * B * C * D) - Matrix.trace (C * B * A * D) =
      4 * Complex.I *
        ((a * w .y - c * u .y) * (v .x * x .z - v .z * x .x) +
          b * (w .y * (u .x * x .z - u .z * x .x) +
            u .y * (w .z * x .x - w .x * x .z)) +
          d * (w .y * (u .z * v .x - u .x * v .z) +
            u .y * (v .z * w .x - v .x * w .z))) := by
  dsimp only
  rw [trace_four_antisymmetric_eq_pauliCoefficients]
  simp [dotProduct_pauliAxis, pauliCross, cross_apply, pauliAxisComponent,
    hB, hD]
  ring

/-- Antisymmetrized Pauli traces with xz-plane middle/final vectors and
transversely related current vectors factor into three bilinear minors.
The relation `w.x = -u.y` is explicit; no Hermiticity is needed. -/
theorem trace_four_antisymmetric_eq_xz_plane_transverse_minors
    (A B C D : PauliMatrix)
    (hB : pauliVectorCoefficient B .y = 0)
    (hD : pauliVectorCoefficient D .y = 0)
    (htrans : pauliVectorCoefficient C .x = -pauliVectorCoefficient A .y) :
    let a := pauliScalarCoefficient A
    let b := pauliScalarCoefficient B
    let c := pauliScalarCoefficient C
    let d := pauliScalarCoefficient D
    let u := pauliVectorCoefficient A
    let v := pauliVectorCoefficient B
    let w := pauliVectorCoefficient C
    let x := pauliVectorCoefficient D
    Matrix.trace (A * B * C * D) - Matrix.trace (C * B * A * D) =
      4 * Complex.I *
        ((a * w .y - c * u .y) * (v .x * x .z - v .z * x .x) +
          (b * x .z - d * v .z) * (w .y * u .x + (u .y) ^ 2) +
          (d * v .x - b * x .x) * (w .y * u .z - u .y * w .z)) := by
  rw [trace_four_antisymmetric_eq_xz_plane_minors A B C D hB hD]
  dsimp only
  rw [htrans]
  ring

/-- For an xz-plane two-level matrix, the antisymmetric trace with the
parity-conjugated final insertion reduces to an entrywise two-current minor.
The identity is purely algebraic and does not assume Hermiticity. -/
theorem trace_parity_antisymmetric_xz_entries
    (A C : PauliMatrix) (b gx gz : ℂ) :
    let B : PauliMatrix := !![b + gz, gx; gx, b - gz]
    Matrix.trace
        (A * (pauliZ * B * pauliZ) * B * (-(pauliZ * C * pauliZ))) -
      Matrix.trace
        (C * (pauliZ * B * pauliZ) * B * (-(pauliZ * A * pauliZ))) =
      -2 * gz *
        (gx * ((A 0 0 + A 1 1) * (C 0 1 - C 1 0) -
          (A 0 1 - A 1 0) * (C 0 0 + C 1 1)) +
          2 * b * (A 0 1 * C 1 0 - A 1 0 * C 0 1)) := by
  dsimp only
  simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
    Fin.sum_univ_two, pauliZ]
  ring

/-- The xz-plane parity-antisymmetric trace in canonical Pauli coefficients.
Only two scalar bilinears survive, with no Hermiticity assumption. -/
theorem trace_parity_antisymmetric_xz_pauliCoefficients
    (A C : PauliMatrix) (b gx gz : ℂ) :
    let B : PauliMatrix := !![b + gz, gx; gx, b - gz]
    Matrix.trace
        (A * (pauliZ * B * pauliZ) * B * (-(pauliZ * C * pauliZ))) -
      Matrix.trace
        (C * (pauliZ * B * pauliZ) * B * (-(pauliZ * A * pauliZ))) =
      8 * Complex.I * gz *
        (gx * (pauliScalarCoefficient A * pauliVectorCoefficient C .y -
          pauliScalarCoefficient C * pauliVectorCoefficient A .y) +
        b * (pauliVectorCoefficient A .y * pauliVectorCoefficient C .x -
          pauliVectorCoefficient A .x * pauliVectorCoefficient C .y)) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  dsimp only
  rw [trace_parity_antisymmetric_xz_entries]
  simp only [pauliScalarCoefficient, pauliVectorCoefficient]
  ring_nf
  simp only [hI]
  ring

/-- Parity-antisymmetric trace for a symmetric middle matrix and the transverse
relation between the two current coefficients. All coefficients are extracted
from the supplied matrices; no Hermiticity or model-specific hypotheses enter. -/
theorem trace_parity_antisymmetric_xz_eq_transverse_minors
    (A B C : PauliMatrix) (hsym : B 0 1 = B 1 0)
    (htrans : pauliVectorCoefficient C .x = -pauliVectorCoefficient A .y) :
    let a := pauliScalarCoefficient A
    let b := pauliScalarCoefficient B
    let c := pauliScalarCoefficient C
    let gx := pauliVectorCoefficient B .x
    let gz := pauliVectorCoefficient B .z
    let u := pauliVectorCoefficient A
    let w := pauliVectorCoefficient C
    Matrix.trace
        (A * (pauliZ * B * pauliZ) * B * (-(pauliZ * C * pauliZ))) -
      Matrix.trace
        (C * (pauliZ * B * pauliZ) * B * (-(pauliZ * A * pauliZ))) =
      8 * Complex.I * gz *
        (gx * (a * w .y - c * u .y) -
          b * ((u .y) ^ 2 + u .x * w .y)) := by
  let b := pauliScalarCoefficient B
  let gx := pauliVectorCoefficient B .x
  let gz := pauliVectorCoefficient B .z
  have hB : B = (!![b + gz, gx; gx, b - gz] : PauliMatrix) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, gx, gz, pauliScalarCoefficient, pauliVectorCoefficient, hsym] <;> ring
  have h := trace_parity_antisymmetric_xz_pauliCoefficients A C b gx gz
  dsimp only at h ⊢
  rw [← hB, htrans] at h
  rw [h]
  ring

/-- Trace of four arbitrary complex two-level matrices expressed only through their canonical
Pauli scalar/vector coefficients. -/
theorem trace_four_eq_pauliCoefficients (A B C D : PauliMatrix) :
    Matrix.trace (A * B * C * D) =
      let a := pauliScalarCoefficient A
      let b := pauliScalarCoefficient B
      let c := pauliScalarCoefficient C
      let d := pauliScalarCoefficient D
      let u := pauliVectorCoefficient A
      let v := pauliVectorCoefficient B
      let w := pauliVectorCoefficient C
      let x := pauliVectorCoefficient D
      2 *
        ((a * b + dotProduct u v) * (c * d + dotProduct w x) +
          dotProduct
            (a • v + b • u + Complex.I • pauliCross u v)
            (c • x + d • w + Complex.I • pauliCross w x)) := by
  simpa only [← eq_pauliAffine_coefficients A,
    ← eq_pauliAffine_coefficients B, ← eq_pauliAffine_coefficients C,
    ← eq_pauliAffine_coefficients D] using
    (trace_four_pauliAffine
      (pauliScalarCoefficient A) (pauliScalarCoefficient B)
      (pauliScalarCoefficient C) (pauliScalarCoefficient D)
      (pauliVectorCoefficient A) (pauliVectorCoefficient B)
      (pauliVectorCoefficient C) (pauliVectorCoefficient D))


/-- Trace between opposite signed Pauli half-sums and arbitrary affine insertions.
The bilinear Bloch-vector norm need not equal one. In the normalized case the
scalar insertions drop out, leaving only the transverse pairing and oriented triple product. -/
theorem trace_oppositePauliProjectors
    (u v w : PauliAxis → ℂ) (c d : ℂ) :
    Matrix.trace
        (((1 / 2 : ℂ) • ((1 : PauliMatrix) - pauliCombination u)) *
          (c • (1 : PauliMatrix) + pauliCombination v) *
          ((1 / 2 : ℂ) • ((1 : PauliMatrix) + pauliCombination u)) *
          (d • (1 : PauliMatrix) + pauliCombination w)) =
      (1 - dotProduct u u) / 2 * c * d +
        (1 + dotProduct u u) / 2 * dotProduct v w -
        dotProduct u v * dotProduct u w -
        Complex.I * dotProduct u (pauliCross v w) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  have hminus : (1 : PauliMatrix) - pauliCombination u =
      (1 : ℂ) • (1 : PauliMatrix) + pauliCombination ((-1 : ℂ) • u) := by
    rw [pauliCombination_smul, neg_one_smul, one_smul, sub_eq_add_neg]
  have hplus : (1 : PauliMatrix) + pauliCombination u =
      (1 : ℂ) • (1 : PauliMatrix) + pauliCombination u := by
    simp
  rw [hminus, hplus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [trace_four_pauliAffine]
  simp [dotProduct_pauliAxis, pauliCross, cross_apply, pauliAxisComponent, smul_eq_mul]
  ring_nf
  simp only [hI]
  ring

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
  let u : PauliAxis → ℂ := fun axis => pauliAxisComponent axis x y z
  have hcombination :
      pauliCombination u = x • pauliX + y • pauliY + z • pauliZ := by
    simp [pauliCombination_eq_components, u, pauliAxisComponent]
  have hdenEq : a ^ 2 - dotProduct u u = a ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
    simp [dotProduct_pauliAxis, u, pauliAxisComponent, pow_two]
    ring
  rw [← hcombination, mul_smul_comm, pauliShift_mul_companion, hdenEq, smul_smul]
  simp [hden]

end InternalSpace
