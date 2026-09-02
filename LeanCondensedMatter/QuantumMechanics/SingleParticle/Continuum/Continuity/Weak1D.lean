import LeanCondensedMatter.Analysis.Calculus.WeakConservation1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Integral1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Scalar1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak one-dimensional Schrödinger continuity equation

This module supplies the probability-density/current specializations of the generic
one-dimensional weak conservation-law kernel.  The integration-by-parts theorem itself lives under
`Analysis.Calculus.WeakConservation1D` and is independent of quantum mechanics.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- Spatially smeared value of the pointwise density time derivative. -/
def intervalSmearedDensityRate1D
    (a b : ℝ) (test densityTimeDerivative : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, test x * densityTimeDerivative x

/-- Pairing of the spatial derivative of a test function with the probability current. -/
def intervalSmearedCurrentPairing1D
    (a b : ℝ) (testDerivative current : ℝ → ℝ) : ℝ :=
  intervalSmearedDensityRate1D a b testDerivative current

/-- Weighted probability-current contribution at the two endpoints of an interval. -/
def weightedBoundaryCurrent1D
    (a b : ℝ) (test current : ℝ → ℝ) : ℝ :=
  test b * current b - test a * current a

/-- The scalar-potential Schrödinger equation gives the one-dimensional interval weak balance.

The wavefunction derivative hypotheses are stated coordinatewise, as in the pointwise continuity
kernel. `hcurrentIntegrable` is the remaining spatial integrability assumption needed for
integration by parts.
-/
theorem schrodinger_weak_continuity_interval
    (a b ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {test testDerivative : ℝ → ℝ}
    {ψ ψt ψx ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        -(κ : ℂ) * ψxx x + (potential x : ℂ) * ψ x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D ℏ κ (ψ x) (ψxx x)) volume a b) :
    intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      intervalSmearedCurrentPairing1D a b testDerivative
          (fun x => probabilityCurrentValue1D ℏ κ (ψ x) (ψx x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => probabilityCurrentValue1D ℏ κ (ψ x) (ψx x)) := by
  have hweak := ConservationLaw.weak_continuity_interval_of_pointwise
    (a := a) (b := b)
    (test := test) (testDerivative := testDerivative)
    (current := fun x => probabilityCurrentValue1D ℏ κ (ψ x) (ψx x))
    (currentDerivative := fun x =>
      probabilityCurrentDivergenceValue1D ℏ κ (ψ x) (ψxx x))
    (densityTimeDerivative := fun x =>
      probabilityDensityTimeDerivativeValue (ψ x) (ψt x))
    (by intro x
        exact probability_continuity_balance_of_schrodinger
          ℏ κ (potential x) (ψ x) (ψt x) (ψxx x) hℏ (hschrodinger x))
    htest
    (by intro x hx
        exact hasDerivAt_probabilityCurrentValue1D ℏ κ
          (hψre x hx) (hψim x hx) (hψxre x hx) (hψxim x hx))
    htestIntegrable hcurrentIntegrable
  simpa [intervalSmearedDensityRate1D, intervalSmearedCurrentPairing1D,
    weightedBoundaryCurrent1D] using hweak

/-- Schrödinger weak continuity for test functions vanishing at the interval endpoints. -/
theorem schrodinger_weak_continuity_interval_zero_boundary
    (a b ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {test testDerivative : ℝ → ℝ}
    {ψ ψt ψx ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        -(κ : ℂ) * ψxx x + (potential x : ℂ) * ψ x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D ℏ κ (ψ x) (ψxx x)) volume a b)
    (ha : test a = 0) (hb : test b = 0) :
    intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      intervalSmearedCurrentPairing1D a b testDerivative
        (fun x => probabilityCurrentValue1D ℏ κ (ψ x) (ψx x)) := by
  rw [schrodinger_weak_continuity_interval a b ℏ κ hℏ htest hψre hψim hψxre hψxim
    hschrodinger htestIntegrable hcurrentIntegrable]
  simp [weightedBoundaryCurrent1D, ha, hb]

/-- Probability-density specialization of the generic interval weak balance. -/
theorem weak_continuity_interval_of_pointwise
    (a b : ℝ)
    {test testDerivative current currentDerivative densityTimeDerivative : ℝ → ℝ}
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable currentDerivative volume a b) :
    intervalSmearedDensityRate1D a b test densityTimeDerivative =
      intervalSmearedCurrentPairing1D a b testDerivative current -
        weightedBoundaryCurrent1D a b test current := by
  have hweak := ConservationLaw.weak_continuity_interval_of_pointwise
    (a := a) (b := b) (test := test) (testDerivative := testDerivative)
    (current := current) (currentDerivative := currentDerivative)
    (densityTimeDerivative := densityTimeDerivative)
    hcontinuity htest hcurrent htestIntegrable hcurrentIntegrable
  simpa [intervalSmearedDensityRate1D, intervalSmearedCurrentPairing1D,
    weightedBoundaryCurrent1D] using hweak

end
end Continuum
end SingleParticle
end QuantumMechanics
