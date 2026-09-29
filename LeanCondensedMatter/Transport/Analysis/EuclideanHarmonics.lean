import Mathlib.LinearAlgebra.Matrix.Module
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
remains generic, so the same decomposition can describe scalars, matrices, or bounded operators.
Sphere measures, spherical-coordinate charts, and dimension-specific harmonic coordinates remain
downstream.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open scoped BigOperators Matrix.Module

/-- Constant, vector, and symmetric-traceless quadratic angular data in `n` dimensions. -/
structure EuclideanHarmonicCoefficients (n : ℕ) (E : Type*) [AddCommMonoid E] where
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

/-- Contract a complex weight vector with a coefficient vector. -/
def contract {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (weights : Fin n → ℂ) (values : Fin n → E) : E :=
  ∑ i, weights i • values i

/-- Complex coordinates of a real direction. -/
def complexDirection {n : ℕ} (direction : Fin n → ℝ) : Fin n → ℂ :=
  fun i => direction i

/-- Evaluate the constant, vector, and symmetric-traceless quadratic harmonics on a real direction. -/
def eval {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E) (direction : Fin n → ℝ) : E :=
  let weights := complexDirection direction
  coefficients.constant +
    contract weights coefficients.first +
      contract weights (fun i => contract weights (coefficients.second i))

/-- Entrywise complexification of a real square matrix. -/
def complexifyMatrix {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  matrix.map Complex.ofRealHom

theorem complexDirection_mulVec {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) (direction : Fin n → ℝ) :
    complexDirection (Matrix.mulVec matrix direction) =
      complexifyMatrix matrix • complexDirection direction := by
  funext i
  simp [complexDirection, complexifyMatrix, Matrix.Module.smul_apply, Matrix.mulVec, dotProduct]

/-- Contraction is contravariant with respect to the matrix-module action. -/
theorem contract_transpose_smul {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (matrix : Matrix (Fin n) (Fin n) ℂ) (weights : Fin n → ℂ) (values : Fin n → E) :
    contract weights (matrix.transpose • values) =
      contract (matrix • weights) values := by
  simp only [contract, Matrix.Module.smul_apply, Matrix.transpose_apply,
    Finset.smul_sum, smul_assoc, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- Contracting each row commutes with the matrix-module action on the row index. -/
theorem contract_matrix_smul_rows {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (weights : Fin n → ℂ) (matrix : Matrix (Fin n) (Fin n) ℂ)
    (rows : Fin n → Fin n → E) :
    (fun i => contract weights ((matrix • rows) i)) =
      matrix • (fun i => contract weights (rows i)) := by
  funext i
  simp only [contract, Matrix.Module.smul_apply, Pi.smul_apply,
    Finset.smul_sum, smul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]

/-- Pull back Euclidean harmonic coefficients along a real orthogonal transformation.
The linear coefficient transforms as `Rᵀ b` and the quadratic coefficient as `Rᵀ Q R`.
The construction is coefficient-generic: only the complex module structure on `E` is used. -/
def orthogonalTransform {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanHarmonicCoefficients n E := by
  let matrixC := complexifyMatrix matrix
  let matrixT := matrixC.transpose
  have hmatrixC : matrixC * matrixC.transpose = 1 := by
    have hmatrix :=
      (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp horthogonal
    change matrix.map Complex.ofRealHom *
        (matrix.map Complex.ofRealHom).transpose = 1
    rw [← Matrix.transpose_map]
    simpa [matrixC, complexifyMatrix] using
      congrArg (fun m : Matrix (Fin n) (Fin n) ℝ => m.map Complex.ofRealHom) hmatrix
  have hentry (k l : Fin n) :
      ∑ i, matrixC k i * matrixC l i = if k = l then 1 else 0 := by
    have h := congrFun (congrFun hmatrixC k) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  refine
    { constant := coefficients.constant
      first := matrixT • coefficients.first
      second := matrixT • (fun k => matrixT • coefficients.second k)
      second_symm := ?_
      second_trace := ?_ }
  · rw [Matrix.IsSymm]
    funext i j
    simp only [Matrix.transpose_apply, Matrix.Module.smul_apply, Pi.smul_apply,
      Finset.smul_sum, smul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    rw [coefficients.second_symm.apply]
    rw [mul_comm]
  · simp only [Matrix.trace, Matrix.Module.smul_apply, Pi.smul_apply,
      Finset.smul_sum, smul_assoc]
    change (∑ i, ∑ k, ∑ l,
      (matrixC k i * matrixC l i) • coefficients.second k l) = 0
    calc
      (∑ i, ∑ k, ∑ l,
          (matrixC k i * matrixC l i) • coefficients.second k l) =
          ∑ k, ∑ l, ∑ i,
            (matrixC k i * matrixC l i) • coefficients.second k l := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.sum_comm]
      _ = ∑ k, ∑ l,
          (∑ i, matrixC k i * matrixC l i) • coefficients.second k l := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            rw [← Finset.sum_smul]
      _ = ∑ k, ∑ l, (if k = l then 1 else 0) • coefficients.second k l := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            rw [hentry]
      _ = Matrix.trace coefficients.second := by
            simp [Matrix.trace]
      _ = 0 := coefficients.second_trace

@[simp]
theorem orthogonalTransform_constant {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    (coefficients.orthogonalTransform matrix horthogonal).constant = coefficients.constant := by
  simp [orthogonalTransform]

@[simp]
theorem orthogonalTransform_first_apply {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    (coefficients.orthogonalTransform matrix horthogonal).first i =
      ∑ j, (((matrix j i : ℝ) : ℂ)) • coefficients.first j := by
  simp [orthogonalTransform, complexifyMatrix, Matrix.Module.smul_apply]

@[simp]
theorem orthogonalTransform_second_apply {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) (i j : Fin n) :
    (coefficients.orthogonalTransform matrix horthogonal).second i j =
      ∑ k, (((matrix k i : ℝ) : ℂ)) •
        ∑ l, (((matrix l j : ℝ) : ℂ)) • coefficients.second k l := by
  simp [orthogonalTransform, complexifyMatrix, Matrix.Module.smul_apply]

/-- Orthogonal pullback of the coefficient data is equivalent to evaluating the original
harmonics on the transformed direction. -/
theorem orthogonalTransform_eval {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (direction : Fin n → ℝ) :
    (coefficients.orthogonalTransform matrix horthogonal).eval direction =
      coefficients.eval (Matrix.mulVec matrix direction) := by
  let matrixC := complexifyMatrix matrix
  let weights := complexDirection direction
  have hdir :
      complexDirection (Matrix.mulVec matrix direction) = matrixC • weights := by
    simpa [matrixC, weights] using complexDirection_mulVec matrix direction
  have hinner (k : Fin n) :
      contract weights (matrixC.transpose • coefficients.second k) =
        contract (matrixC • weights) (coefficients.second k) :=
    contract_transpose_smul matrixC weights (coefficients.second k)
  simp only [eval, orthogonalTransform]
  change
    coefficients.constant +
        contract weights (matrixC.transpose • coefficients.first) +
          contract weights
            (fun i =>
              contract weights
                ((matrixC.transpose •
                  (fun k => matrixC.transpose • coefficients.second k)) i)) =
      coefficients.constant +
        contract (complexDirection (Matrix.mulVec matrix direction)) coefficients.first +
          contract (complexDirection (Matrix.mulVec matrix direction))
            (fun i =>
              contract (complexDirection (Matrix.mulVec matrix direction))
                (coefficients.second i))
  rw [contract_transpose_smul matrixC weights coefficients.first, hdir]
  have hrows :=
    contract_matrix_smul_rows weights matrixC.transpose
      (fun k => matrixC.transpose • coefficients.second k)
  rw [hrows]
  rw [contract_transpose_smul matrixC weights
    (fun k => contract weights (matrixC.transpose • coefficients.second k))]
  simp_rw [hinner]
  rw [hdir]

end EuclideanHarmonicCoefficients

end

end Transport
end QuantumTheory
