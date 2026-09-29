import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Analysis.EuclideanHarmonics
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Planar angular harmonics

Two-dimensional polar-coordinate specialization of the dimension-independent Euclidean harmonic
representation. This module owns the bridge between trigonometric coefficients and vector/STF
tensor data, including planar rotations.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open scoped BigOperators

/-- Unit direction used by the ordinary two-dimensional polar chart. -/
def polarDirection2D (angle : ℝ) : Fin 2 → ℝ :=
  ![Real.cos angle, Real.sin angle]

/-- Counterclockwise rotation matrix in the two-dimensional polar plane. -/
def rotationMatrix2D (angle : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos angle, -Real.sin angle;
     Real.sin angle, Real.cos angle]

/-- Polar unit directions transform by the ordinary two-dimensional rotation matrix. -/
theorem polarDirection2D_add (θ angle : ℝ) :
    polarDirection2D (θ + angle) =
      Matrix.mulVec (rotationMatrix2D angle) (polarDirection2D θ) := by
  funext i
  fin_cases i <;>
    simp [polarDirection2D, rotationMatrix2D, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;>
    ring

/-- Interpret the existing two-dimensional trigonometric coefficients as vector and
symmetric-traceless quadratic Euclidean harmonic data. The mixed coefficient is split equally
between the two off-diagonal matrix entries because both contribute to the quadratic contraction. -/
def AngularHarmonicCoefficients.toEuclidean2D
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) : EuclideanHarmonicCoefficients 2 E := by
  letI := Module.addCommMonoidToAddCommGroup ℂ (M := E)
  exact
    { constant := coefficients.constant
      first := ![coefficients.firstCosine, coefficients.firstSine]
      second :=
        !![coefficients.secondCosine, (2 : ℂ)⁻¹ • coefficients.secondMixed;
           (2 : ℂ)⁻¹ • coefficients.secondMixed, -coefficients.secondCosine]
      second_symm := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      second_trace := by
        simp [Matrix.trace, Fin.sum_univ_two] }

-- The bridge proof intentionally uses `simp` to normalize finite vector/matrix notation before
-- coefficient comparison.
set_option linter.flexible false in
/-- The legacy two-dimensional trigonometric evaluation is exactly the Euclidean vector/STF
quadratic evaluation on the polar unit direction. -/
theorem AngularHarmonicCoefficients.eval_eq_toEuclidean2D_eval
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    coefficients.eval angle =
      coefficients.toEuclidean2D.eval (polarDirection2D angle) := by
  letI := Module.addCommMonoidToAddCommGroup ℂ (M := E)
  simp [AngularHarmonicCoefficients.eval, AngularHarmonicCoefficients.toEuclidean2D,
    EuclideanHarmonicCoefficients.eval, EuclideanHarmonicCoefficients.contract,
    EuclideanHarmonicCoefficients.complexDirection, polarDirection2D, Fin.sum_univ_two,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  match_scalars <;>
    (try rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]) <;>
    simp only [Complex.coe_algebraMap] <;>
    ring

/-- Convert two-dimensional Euclidean STF data back to the legacy trigonometric coordinates. -/
def EuclideanHarmonicCoefficients.toAngular2D
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients 2 E) : AngularHarmonicCoefficients E where
  constant := coefficients.constant
  firstCosine := coefficients.first 0
  firstSine := coefficients.first 1
  secondCosine := coefficients.second 0 0
  secondMixed := (2 : ℂ) • coefficients.second 0 1

-- The inverse bridge uses the same finite-coordinate normalization strategy.
set_option linter.flexible false in
/-- The Euclidean-to-trigonometric bridge preserves evaluation on the polar unit direction. -/
theorem EuclideanHarmonicCoefficients.toAngular2D_eval
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients 2 E) (angle : ℝ) :
    coefficients.toAngular2D.eval angle =
      coefficients.eval (polarDirection2D angle) := by
  letI := Module.addCommMonoidToAddCommGroup ℂ (M := E)
  have hdiag : coefficients.second 1 1 = -coefficients.second 0 0 := by
    have h : coefficients.second 0 0 + coefficients.second 1 1 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using coefficients.second_trace
    exact eq_neg_of_add_eq_zero_right h
  have hoff : coefficients.second 1 0 = coefficients.second 0 1 := by
    have h := congrFun (congrFun coefficients.second_symm 0) 1
    simpa using h
  simp [EuclideanHarmonicCoefficients.toAngular2D, AngularHarmonicCoefficients.eval,
    EuclideanHarmonicCoefficients.eval, EuclideanHarmonicCoefficients.contract,
    EuclideanHarmonicCoefficients.complexDirection, polarDirection2D, Fin.sum_univ_two, hdiag, hoff,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  match_scalars <;>
    (try rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]) <;>
    simp only [Complex.coe_algebraMap] <;>
    ring

/-- The ordinary planar rotation matrix is orthogonal. -/
theorem rotationMatrix2D_mem_orthogonalGroup (angle : ℝ) :
    rotationMatrix2D angle ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix2D, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq angle]

/-- Rotate two-dimensional trigonometric coefficients by specializing the generic Euclidean
orthogonal pullback. -/
def AngularHarmonicCoefficients.rotate2D
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    AngularHarmonicCoefficients E :=
  ((coefficients.toEuclidean2D).orthogonalTransform
      (rotationMatrix2D angle) (rotationMatrix2D_mem_orthogonalGroup angle)).toAngular2D

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_constant
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    (coefficients.rotate2D angle).constant = coefficients.constant := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    AngularHarmonicCoefficients.toEuclidean2D]

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_firstCosine
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    (coefficients.rotate2D angle).firstCosine =
      ((Real.cos angle : ℝ) : ℂ) • coefficients.firstCosine +
        ((Real.sin angle : ℝ) : ℂ) • coefficients.firstSine := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D, Fin.sum_univ_two]

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_firstSine
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    (coefficients.rotate2D angle).firstSine =
      (-((Real.sin angle : ℝ) : ℂ)) • coefficients.firstCosine +
        ((Real.cos angle : ℝ) : ℂ) • coefficients.firstSine := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D, Fin.sum_univ_two]

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_secondCosine
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    (coefficients.rotate2D angle).secondCosine =
      ((((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) •
          coefficients.secondCosine) +
        (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) •
          coefficients.secondMixed := by
  letI := Module.addCommMonoidToAddCommGroup ℂ (M := E)
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D, Fin.sum_univ_two]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  module

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_secondMixed
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    (coefficients.rotate2D angle).secondMixed =
      ((-4 : ℂ) * (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ))) •
          coefficients.secondCosine +
        ((((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) •
          coefficients.secondMixed) := by
  letI := Module.addCommMonoidToAddCommGroup ℂ (M := E)
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D, Fin.sum_univ_two]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  module

/-- Rotating the coefficient data is equivalent to shifting the polar direction. -/
theorem AngularHarmonicCoefficients.rotate2D_eval
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle θ : ℝ) :
    (coefficients.rotate2D angle).eval θ = coefficients.eval (θ + angle) := by
  rw [AngularHarmonicCoefficients.rotate2D,
    EuclideanHarmonicCoefficients.toAngular2D_eval,
    EuclideanHarmonicCoefficients.orthogonalTransform_eval,
    ← polarDirection2D_add,
    ← AngularHarmonicCoefficients.eval_eq_toEuclidean2D_eval]

end

end Transport
end QuantumTheory
