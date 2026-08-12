import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuity
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Integrated probability quantities in one dimension

This module owns the probability-density integrals used by both the continuity-equation and
operator-theoretic developments.  The definitions do not depend on Schrödinger dynamics, dominated
differentiation, or any particular conservation theorem.
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

/-- Total probability of a one-dimensional wavefunction. -/
def totalProbability1D (ψ : ℝ → ℂ) : ℝ :=
  ∫ x, probabilityDensityValue (ψ x)

end
end Continuum
end SingleParticle
end QuantumMechanics
