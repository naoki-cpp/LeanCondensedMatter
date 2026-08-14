import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Basic1D
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Integrated probability quantities in one dimension

This module owns the probability- and charge-density integrals used by both the continuity-equation
and operator-theoretic developments. The definitions depend only on the pointwise probability
foundation, not on Schrödinger dynamics, dominated differentiation, or any particular conservation
theorem.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped Interval

/-- Probability density smeared against a real spatial test function on an interval. -/
def intervalSmearedProbabilityDensity1D
    (a b : ℝ) (test : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∫ x in a..b, test x * probabilityDensityValue (ψ x)

/-- Probability density smeared against a real spatial test function over all of one-dimensional
space. -/
def wholeSpaceSmearedProbabilityDensity1D
    (test : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∫ x, test x * probabilityDensityValue (ψ x)

/-- Charge density smeared against a real spatial test function over all of one-dimensional space. -/
def wholeSpaceSmearedChargeDensity1D
    (q : ℝ) (test : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∫ x, test x * chargeDensityValue q (ψ x)

/-- Smeared charge density is the particle charge times smeared probability density. -/
theorem wholeSpaceSmearedChargeDensity1D_eq_charge_mul_probability
    (q : ℝ) (test : ℝ → ℝ) (ψ : ℝ → ℂ) :
    wholeSpaceSmearedChargeDensity1D q test ψ =
      q * wholeSpaceSmearedProbabilityDensity1D test ψ := by
  unfold wholeSpaceSmearedChargeDensity1D wholeSpaceSmearedProbabilityDensity1D
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp [chargeDensityValue]
  ring

/-- Total probability of a one-dimensional wavefunction. -/
def totalProbability1D (ψ : ℝ → ℂ) : ℝ :=
  ∫ x, probabilityDensityValue (ψ x)

end
end Continuum
end SingleParticle
end QuantumMechanics
