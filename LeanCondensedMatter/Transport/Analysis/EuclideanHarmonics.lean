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

open scoped BigOperators

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

/-- Evaluate constant, vector, and STF quadratic data on a real direction. -/
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

/-- Pull back a coefficient vector along a complex matrix. -/
def pullbackVector {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (matrix : Matrix (Fin n) (Fin n) ℂ) (values : Fin n → E) : Fin n → E :=
  fun i => ∑ j, matrix j i • values j

/-- Pull back both indices of a coefficient matrix along a complex matrix. -/
def pullbackMatrix {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (matrix : Matrix (Fin n) (Fin n) ℂ)
    (values : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  pullbackVector matrix (fun k => pullbackVector matrix (values k))

theorem complexDirection_mulVec {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) (direction : Fin n → ℝ) :
    complexDirection (Matrix.mulVec matrix direction) =
      Matrix.mulVec (complexifyMatrix matrix) (complexDirection direction) := by
  funext i
  simp [complexDirection, complexifyMatrix, Matrix.mulVec, dotProduct]

/-- Contraction is contravariant with respect to coefficient-vector pullback. -/
theorem contract_pullbackVector {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (matrix : Matrix (Fin n) (Fin n) ℂ) (weights : Fin n → ℂ) (values : Fin n → E) :
    contract weights (pullbackVector matrix values) =
      contract (Matrix.mulVec matrix weights) values := by
  simp only [contract, pullbackVector, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- Contracting each row commutes with pullback of the row index. -/
theorem contract_pullbackRows {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (weights : Fin n → ℂ) (matrix : Matrix (Fin n) (Fin n) ℂ)
    (rows : Fin n → Fin n → E) :
    (fun i => contract weights ((pullbackVector matrix rows) i)) =
      pullbackVector matrix (fun i => contract weights (rows i)) := by
  funext i
  simp only [contract, pullbackVector, Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- Quadratic contraction is contravariant in both indices. -/
theorem quadraticContract_pullbackMatrix {n : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℂ E]
    (matrix : Matrix (Fin n) (Fin n) ℂ) (weights : Fin n → ℂ)
    (values : Matrix (Fin n) (Fin n) E) :
    contract weights (fun i => contract weights (pullbackMatrix matrix values i)) =
      contract (Matrix.mulVec matrix weights)
        (fun i => contract (Matrix.mulVec matrix weights) (values i)) := by
  simp only [pullbackMatrix]
  rw [contract_pullbackRows, contract_pullbackVector]
  congr 1
  funext k
  exact contract_pullbackVector matrix weights (values k)

/-- Pullback of a symmetric coefficient matrix is symmetric. -/
theorem pullbackMatrix_isSymm {n : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℂ E]
    (matrix : Matrix (Fin n) (Fin n) ℂ)
    {values : Matrix (Fin n) (Fin n) E} (hvalues : values.IsSymm) :
    (pullbackMatrix matrix values).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [pullbackMatrix, pullbackVector, Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [hvalues.apply]
  rw [mul_comm]

/-- Pull back Euclidean harmonic coefficients along a real orthogonal transformation.
The linear coefficient transforms as `Rᵀ b` and the quadratic coefficient as `Rᵀ Q R`.
The construction is coefficient-generic. -/
def orthogonalTransform {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanHarmonicCoefficients n E := by
  let matrixC := complexifyMatrix matrix
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
  have htrace : Matrix.trace (pullbackMatrix matrixC coefficients.second) = 0 := by
    simp only [Matrix.trace, Matrix.diag, pullbackMatrix, pullbackVector,
      Finset.sum_apply, Pi.smul_apply]
    simp_rw [Finset.smul_sum, ← mul_smul]
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
            rw [Finset.sum_smul]
      _ = ∑ k, ∑ l, (if k = l then 1 else 0) • coefficients.second k l := by
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            simp [hentry]
      _ = Matrix.trace coefficients.second := by
            simp [Matrix.trace]
      _ = 0 := coefficients.second_trace
  exact
    { constant := coefficients.constant
      first := pullbackVector matrixC coefficients.first
      second := pullbackMatrix matrixC coefficients.second
      second_symm := pullbackMatrix_isSymm matrixC coefficients.second_symm
      second_trace := htrace }

@[simp]
theorem orthogonalTransform_constant {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    (coefficients.orthogonalTransform matrix horthogonal).constant = coefficients.constant := by
  simp [orthogonalTransform]

@[simp]
theorem orthogonalTransform_first_apply {n : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    (coefficients.orthogonalTransform matrix horthogonal).first i =
      ∑ j, (((matrix j i : ℝ) : ℂ)) • coefficients.first j := by
  simp [orthogonalTransform, pullbackVector, complexifyMatrix]

@[simp]
theorem orthogonalTransform_second_apply {n : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ) (i j : Fin n) :
    (coefficients.orthogonalTransform matrix horthogonal).second i j =
      ∑ k, (((matrix k i : ℝ) : ℂ)) •
        ∑ l, (((matrix l j : ℝ) : ℂ)) • coefficients.second k l := by
  simp [orthogonalTransform, pullbackMatrix, pullbackVector, complexifyMatrix,
    Finset.sum_apply, Pi.smul_apply]

/-- Orthogonal pullback of the coefficient data is equivalent to evaluating the original
harmonics on the transformed direction. -/
theorem orthogonalTransform_eval {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E)
    (matrix : Matrix (Fin n) (Fin n) ℝ)
    (horthogonal : matrix ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (direction : Fin n → ℝ) :
    (coefficients.orthogonalTransform matrix horthogonal).eval direction =
      coefficients.eval (Matrix.mulVec matrix direction) := by
  let matrixC := complexifyMatrix matrix
  let weights := complexDirection direction
  have hdir :
      complexDirection (Matrix.mulVec matrix direction) =
        Matrix.mulVec matrixC weights := by
    simpa [matrixC, weights] using complexDirection_mulVec matrix direction
  simp only [eval]
  change
    coefficients.constant +
        contract weights (pullbackVector matrixC coefficients.first) +
          contract weights
            (fun i => contract weights (pullbackMatrix matrixC coefficients.second i)) =
      coefficients.constant +
        contract (complexDirection (Matrix.mulVec matrix direction)) coefficients.first +
          contract (complexDirection (Matrix.mulVec matrix direction))
            (fun i =>
              contract (complexDirection (Matrix.mulVec matrix direction))
                (coefficients.second i))
  rw [contract_pullbackVector, quadraticContract_pullbackMatrix, hdir]

end EuclideanHarmonicCoefficients

end

end Transport
end QuantumTheory
