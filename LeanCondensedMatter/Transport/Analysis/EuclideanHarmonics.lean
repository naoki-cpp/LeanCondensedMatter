import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Euclidean angular harmonics

Coordinate representation of the degree-zero, degree-one, and degree-two angular data that underlie
transport angular reductions in arbitrary finite dimension.

The first harmonic is a vector. The second harmonic is represented by a symmetric traceless matrix,
so evaluation on a direction `ω` is the quadratic contraction `ωᵢ ωⱼ Qᵢⱼ`. The coefficient type
remains generic, matching `AngularHarmonicCoefficients`, so the same decomposition can describe
scalars, matrices, or bounded operators. Sphere measures and spherical-coordinate charts remain
downstream.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open scoped BigOperators

/-- Constant, vector, and symmetric-traceless quadratic angular data in `n` dimensions. -/
structure EuclideanHarmonicCoefficients (n : ℕ) (E : Type*) [AddCommGroup E] where
  /-- Degree-zero harmonic. -/
  constant : E
  /-- Degree-one harmonic coefficients. -/
  first : Fin n → E
  /-- Degree-two harmonic coefficients. -/
  second : Matrix (Fin n) (Fin n) E
  /-- The quadratic coefficient is symmetric. -/
  second_symm : second.IsSymm
  /-- The quadratic coefficient is traceless. -/
  second_trace : Matrix.trace second = 0

namespace EuclideanHarmonicCoefficients

/-- Evaluate the constant, vector, and symmetric-traceless quadratic harmonics on a real direction. -/
def eval {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E) (direction : Fin n → ℝ) : E :=
  coefficients.constant +
    ∑ i, ((direction i : ℝ) : ℂ) • coefficients.first i +
      ∑ i, ∑ j,
        ((((direction i : ℝ) : ℂ) * ((direction j : ℝ) : ℂ))) • coefficients.second i j

/-- Entrywise complexification of a real square matrix. -/
def complexifyMatrix {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  matrix.map Complex.ofRealHom

/-- Entrywise complexification of a real direction vector. -/
def complexDirection {n : ℕ} (direction : Fin n → ℝ) : Fin n → ℂ :=
  fun i => direction i

theorem complexDirection_mulVec {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) (direction : Fin n → ℝ) :
    complexDirection (Matrix.mulVec matrix direction) =
      Matrix.mulVec (complexifyMatrix matrix) (complexDirection direction) := by
  funext i
  simp [complexDirection, complexifyMatrix, Matrix.mulVec, dotProduct]

/-- For complex coefficients, Euclidean harmonic evaluation is the familiar linear plus quadratic
matrix contraction. -/
theorem eval_eq_dotProduct {n : ℕ}
    (coefficients : EuclideanHarmonicCoefficients n ℂ) (direction : Fin n → ℝ) :
    coefficients.eval direction =
      coefficients.constant +
        complexDirection direction ⬝ᵥ coefficients.first +
        complexDirection direction ⬝ᵥ
          Matrix.mulVec coefficients.second (complexDirection direction) := by
  simp only [eval, complexDirection, Matrix.mulVec, dotProduct, Finset.mul_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Pull back complex Euclidean harmonic coefficients along a real orthogonal transformation.
The linear coefficient transforms as `Rᵀ b` and the quadratic coefficient as `Rᵀ Q R`. -/
def orthogonalTransform {n : ℕ}
    (coefficients : EuclideanHarmonicCoefficients n ℂ)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanHarmonicCoefficients n ℂ := by
  let matrixC := complexifyMatrix matrix
  have hmatrixC : matrixC * matrixC.transpose = 1 := by
    have hmatrix :=
      (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp horthogonal
    change matrix.map Complex.ofRealHom *
        (matrix.map Complex.ofRealHom).transpose = 1
    rw [← Matrix.transpose_map]
    simpa [matrixC, complexifyMatrix] using
      congrArg (fun m : Matrix (Fin n) (Fin n) ℝ => m.map Complex.ofRealHom) hmatrix
  refine
    { constant := coefficients.constant
      first := Matrix.mulVec matrixC.transpose coefficients.first
      second := matrixC.transpose * coefficients.second * matrixC
      second_symm := ?_
      second_trace := ?_ }
  · rw [Matrix.IsSymm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [coefficients.second_symm, Matrix.mul_assoc]
  · calc
      Matrix.trace (matrixC.transpose * coefficients.second * matrixC) =
          Matrix.trace (matrixC * matrixC.transpose * coefficients.second) := by
            exact Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace coefficients.second := by rw [hmatrixC, Matrix.one_mul]
      _ = 0 := coefficients.second_trace

/-- Orthogonal pullback of the coefficient data is equivalent to evaluating the original
harmonics on the transformed direction. -/
theorem orthogonalTransform_eval {n : ℕ}
    (coefficients : EuclideanHarmonicCoefficients n ℂ)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (direction : Fin n → ℝ) :
    (coefficients.orthogonalTransform matrix horthogonal).eval direction =
      coefficients.eval (Matrix.mulVec matrix direction) := by
  rw [eval_eq_dotProduct, eval_eq_dotProduct, complexDirection_mulVec]
  simp only [orthogonalTransform, Matrix.mulVec_mulVec, dotProduct_comm]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

end EuclideanHarmonicCoefficients

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
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) : EuclideanHarmonicCoefficients 2 E where
  constant := coefficients.constant
  first := ![coefficients.firstCosine, coefficients.firstSine]
  second :=
    !![coefficients.secondCosine, (2 : ℂ)⁻¹ • coefficients.secondMixed;
       (2 : ℂ)⁻¹ • coefficients.secondMixed, -coefficients.secondCosine]
  second_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  second_trace := by
    simp [Matrix.trace, Fin.sum_univ_two]

/-- The legacy two-dimensional trigonometric evaluation is exactly the Euclidean vector/STF
quadratic evaluation on the polar unit direction. -/
theorem AngularHarmonicCoefficients.eval_eq_toEuclidean2D_eval
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    coefficients.eval angle =
      coefficients.toEuclidean2D.eval (polarDirection2D angle) := by
  simp [AngularHarmonicCoefficients.eval, AngularHarmonicCoefficients.toEuclidean2D,
    EuclideanHarmonicCoefficients.eval, polarDirection2D, Fin.sum_univ_two,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  module

/-- Convert two-dimensional Euclidean STF data back to the legacy trigonometric coordinates. -/
def EuclideanHarmonicCoefficients.toAngular2D
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients 2 E) : AngularHarmonicCoefficients E where
  constant := coefficients.constant
  firstCosine := coefficients.first 0
  firstSine := coefficients.first 1
  secondCosine := coefficients.second 0 0
  secondMixed := (2 : ℂ) • coefficients.second 0 1

/-- The Euclidean-to-trigonometric bridge preserves evaluation on the polar unit direction. -/
theorem EuclideanHarmonicCoefficients.toAngular2D_eval
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients 2 E) (angle : ℝ) :
    coefficients.toAngular2D.eval angle =
      coefficients.eval (polarDirection2D angle) := by
  have hdiag : coefficients.second 1 1 = -coefficients.second 0 0 := by
    have h : coefficients.second 0 0 + coefficients.second 1 1 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using coefficients.second_trace
    exact eq_neg_of_add_eq_zero_right h
  have hoff : coefficients.second 1 0 = coefficients.second 0 1 := by
    have h := congrFun (congrFun coefficients.second_symm 0) 1
    simpa using h
  simp [EuclideanHarmonicCoefficients.toAngular2D, AngularHarmonicCoefficients.eval,
    EuclideanHarmonicCoefficients.eval, polarDirection2D, Fin.sum_univ_two, hdiag, hoff,
    -Complex.ofReal_cos, -Complex.ofReal_sin]
  module

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
    (coefficients : AngularHarmonicCoefficients ℂ) (angle : ℝ) :
    AngularHarmonicCoefficients ℂ :=
  ((coefficients.toEuclidean2D).orthogonalTransform
      (rotationMatrix2D angle) (rotationMatrix2D_mem_orthogonalGroup angle)).toAngular2D


@[simp]
theorem AngularHarmonicCoefficients.rotate2D_constant
    (coefficients : AngularHarmonicCoefficients ℂ) (angle : ℝ) :
    (coefficients.rotate2D angle).constant = coefficients.constant := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    EuclideanHarmonicCoefficients.orthogonalTransform,
    AngularHarmonicCoefficients.toEuclidean2D]

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_firstCosine
    (coefficients : AngularHarmonicCoefficients ℂ) (angle : ℝ) :
    (coefficients.rotate2D angle).firstCosine =
      ((Real.cos angle : ℝ) : ℂ) * coefficients.firstCosine +
        ((Real.sin angle : ℝ) : ℂ) * coefficients.firstSine := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    EuclideanHarmonicCoefficients.orthogonalTransform,
    EuclideanHarmonicCoefficients.complexifyMatrix,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_firstSine
    (coefficients : AngularHarmonicCoefficients ℂ) (angle : ℝ) :
    (coefficients.rotate2D angle).firstSine =
      -((Real.sin angle : ℝ) : ℂ) * coefficients.firstCosine +
        ((Real.cos angle : ℝ) : ℂ) * coefficients.firstSine := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    EuclideanHarmonicCoefficients.orthogonalTransform,
    EuclideanHarmonicCoefficients.complexifyMatrix,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_secondCosine
    (coefficients : AngularHarmonicCoefficients ℂ) (angle : ℝ) :
    (coefficients.rotate2D angle).secondCosine =
      (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) *
          coefficients.secondCosine +
        ((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ) *
          coefficients.secondMixed := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    EuclideanHarmonicCoefficients.orthogonalTransform,
    EuclideanHarmonicCoefficients.complexifyMatrix,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[simp]
theorem AngularHarmonicCoefficients.rotate2D_secondMixed
    (coefficients : AngularHarmonicCoefficients ℂ) (angle : ℝ) :
    (coefficients.rotate2D angle).secondMixed =
      -4 * (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
          coefficients.secondCosine +
        (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) *
          coefficients.secondMixed := by
  simp [AngularHarmonicCoefficients.rotate2D, EuclideanHarmonicCoefficients.toAngular2D,
    EuclideanHarmonicCoefficients.orthogonalTransform,
    EuclideanHarmonicCoefficients.complexifyMatrix,
    AngularHarmonicCoefficients.toEuclidean2D, rotationMatrix2D,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Rotating the coefficient data is equivalent to shifting the polar direction. -/
theorem AngularHarmonicCoefficients.rotate2D_eval
    (coefficients : AngularHarmonicCoefficients ℂ) (angle θ : ℝ) :
    (coefficients.rotate2D angle).eval θ = coefficients.eval (θ + angle) := by
  rw [AngularHarmonicCoefficients.rotate2D,
    EuclideanHarmonicCoefficients.toAngular2D_eval,
    EuclideanHarmonicCoefficients.orthogonalTransform_eval,
    ← polarDirection2D_add,
    ← AngularHarmonicCoefficients.eval_eq_toEuclidean2D_eval]

end

end Transport
end QuantumTheory
