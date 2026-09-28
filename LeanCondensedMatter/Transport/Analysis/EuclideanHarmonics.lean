import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Euclidean angular harmonics

Coordinate representation of the degree-zero, degree-one, and degree-two angular data that underlie
transport angular reductions in arbitrary finite dimension.

The first harmonic is a vector. The second harmonic is represented by a symmetric traceless matrix,
so evaluation on a direction `ω` is the quadratic form `ωᵀ Q ω`. This module only owns the
algebraic harmonic data; sphere measures and spherical-coordinate charts remain downstream.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open scoped BigOperators

/-- Constant, vector, and symmetric-traceless quadratic angular data in `n` dimensions. -/
structure EuclideanHarmonicCoefficients (n : ℕ) where
  /-- Degree-zero harmonic. -/
  constant : ℂ
  /-- Degree-one harmonic coefficients. -/
  first : Fin n → ℂ
  /-- Degree-two harmonic coefficients. -/
  second : Matrix (Fin n) (Fin n) ℂ
  /-- The quadratic coefficient is symmetric. -/
  second_symm : second.IsSymm
  /-- The quadratic coefficient is traceless. -/
  second_trace : Matrix.trace second = 0

namespace EuclideanHarmonicCoefficients

/-- Evaluate the constant, vector, and symmetric-traceless quadratic harmonics on a real direction. -/
def eval {n : ℕ} (coefficients : EuclideanHarmonicCoefficients n)
    (direction : Fin n → ℝ) : ℂ :=
  coefficients.constant +
    ∑ i, ((direction i : ℝ) : ℂ) * coefficients.first i +
      ∑ i, ∑ j,
        ((direction i : ℝ) : ℂ) * ((direction j : ℝ) : ℂ) * coefficients.second i j

end EuclideanHarmonicCoefficients

/-- Unit direction used by the ordinary two-dimensional polar chart. -/
def polarDirection2D (angle : ℝ) : Fin 2 → ℝ :=
  ![Real.cos angle, Real.sin angle]

/-- Interpret the existing two-dimensional trigonometric coefficients as vector and
symmetric-traceless quadratic Euclidean harmonic data. The mixed coefficient is split equally
between the two off-diagonal matrix entries because both contribute to `ωᵀ Q ω`. -/
def AngularHarmonicCoefficients.toEuclidean2D
    (coefficients : AngularHarmonicCoefficients ℂ) : EuclideanHarmonicCoefficients 2 where
  constant := coefficients.constant
  first := ![coefficients.firstCosine, coefficients.firstSine]
  second :=
    !![coefficients.secondCosine, coefficients.secondMixed / 2;
       coefficients.secondMixed / 2, -coefficients.secondCosine]
  second_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  second_trace := by
    simp [Matrix.trace, Fin.sum_univ_two]

/-- The legacy two-dimensional trigonometric evaluation is exactly the Euclidean vector/STF
quadratic evaluation on the polar unit direction. -/
theorem AngularHarmonicCoefficients.eval_eq_toEuclidean2D_eval
    (coefficients : AngularHarmonicCoefficients ℂ) (angle : ℝ) :
    coefficients.eval angle =
      coefficients.toEuclidean2D.eval (polarDirection2D angle) := by
  simp [AngularHarmonicCoefficients.eval, AngularHarmonicCoefficients.toEuclidean2D,
    EuclideanHarmonicCoefficients.eval, polarDirection2D, Fin.sum_univ_two, smul_eq_mul]
  ring

end

end Transport
end QuantumTheory
