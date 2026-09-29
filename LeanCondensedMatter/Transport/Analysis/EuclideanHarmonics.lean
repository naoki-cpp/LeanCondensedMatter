import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import Mathlib.LinearAlgebra.Matrix.Trace
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

/-- Evaluate the constant, vector, and symmetric-traceless quadratic harmonics on a real direction. -/
def eval {n : ℕ} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : EuclideanHarmonicCoefficients n E) (direction : Fin n → ℝ) : E :=
  coefficients.constant +
    ∑ i, ((direction i : ℝ) : ℂ) • coefficients.first i +
      ∑ i, ∑ j,
        ((((direction i : ℝ) : ℂ) * ((direction j : ℝ) : ℂ))) • coefficients.second i j

end EuclideanHarmonicCoefficients

/-- Unit direction used by the ordinary two-dimensional polar chart. -/
def polarDirection2D (angle : ℝ) : Fin 2 → ℝ :=
  ![Real.cos angle, Real.sin angle]

/-- Interpret the existing two-dimensional trigonometric coefficients as vector and
symmetric-traceless quadratic Euclidean harmonic data. The mixed coefficient is split equally
between the two off-diagonal matrix entries because both contribute to the quadratic contraction. -/
def AngularHarmonicCoefficients.toEuclidean2D
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) : EuclideanHarmonicCoefficients 2 E where
  constant := coefficients.constant
  first := ![coefficients.firstCosine, coefficients.firstSine]
  second :=
    !![coefficients.secondCosine, (2 : ℂ)⁻¹ • coefficients.secondMixed;
       (2 : ℂ)⁻¹ • coefficients.secondMixed, -coefficients.secondCosine]
  second_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  second_trace := by
    simp [Matrix.trace, Fin.sum_univ_two]

/-- The legacy two-dimensional trigonometric evaluation is exactly the Euclidean vector/STF
quadratic evaluation on the polar unit direction. -/
theorem AngularHarmonicCoefficients.eval_eq_toEuclidean2D_eval
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle : ℝ) :
    coefficients.eval angle =
      coefficients.toEuclidean2D.eval (polarDirection2D angle) := by
  simp [AngularHarmonicCoefficients.eval, AngularHarmonicCoefficients.toEuclidean2D,
    EuclideanHarmonicCoefficients.eval, polarDirection2D, Fin.sum_univ_two]
  module

/-- Shifting the polar angle is evaluation of the same Euclidean harmonic data on the shifted
unit direction. This is the coordinate-free replacement for expanding every first- and
second-harmonic trigonometric coefficient under angle addition. -/
theorem AngularHarmonicCoefficients.eval_add_eq_toEuclidean2D_eval
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (angle θ : ℝ) :
    coefficients.eval (θ + angle) =
      coefficients.toEuclidean2D.eval (polarDirection2D (θ + angle)) :=
  coefficients.eval_eq_toEuclidean2D_eval (θ + angle)

end

end Transport
end QuantumTheory
