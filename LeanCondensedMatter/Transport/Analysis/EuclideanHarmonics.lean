import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Euclidean angular harmonics

Coordinate representation of the degree-zero, degree-one, and degree-two angular data that underlie
transport angular reductions in arbitrary finite dimension.

The first harmonic is a vector. The second harmonic is represented by a symmetric traceless matrix,
so evaluation on a direction `ω` is the quadratic contraction `ωᵢ ωⱼ Qᵢⱼ`. The coefficient type remains generic, so the same decomposition can describe scalars, matrices, or
bounded operators. Sphere measures, spherical-coordinate charts, and dimension-specific harmonic
coordinates remain downstream.
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
  congr 1
  · rw [Matrix.dotProduct_transpose_mulVec]
  · calc
      complexDirection direction ⬝ᵥ
          ((complexifyMatrix matrix).transpose * coefficients.second * complexifyMatrix matrix).mulVec
            (complexDirection direction) =
        complexDirection direction ⬝ᵥ
          (complexifyMatrix matrix).transpose.mulVec
            ((coefficients.second * complexifyMatrix matrix).mulVec
              (complexDirection direction)) := by
          rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      _ = (coefficients.second * complexifyMatrix matrix).mulVec (complexDirection direction) ⬝ᵥ
          (complexifyMatrix matrix).mulVec (complexDirection direction) := by
        exact Matrix.dotProduct_transpose_mulVec _ _ _
      _ = (complexifyMatrix matrix).mulVec (complexDirection direction) ⬝ᵥ
          (coefficients.second * complexifyMatrix matrix).mulVec (complexDirection direction) :=
        dotProduct_comm _ _

end EuclideanHarmonicCoefficients

end

end Transport
end QuantumTheory
