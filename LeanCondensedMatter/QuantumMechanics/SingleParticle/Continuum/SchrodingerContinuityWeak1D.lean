import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak one-dimensional Schrödinger continuity equation

This module turns the pointwise one-dimensional continuity equation into an interval-smeared
identity. The boundary term is kept explicit first; test functions vanishing at the endpoints then
recover the usual weak continuity equation.

At this stage the theorem concerns the spatial integral of the pointwise density time-derivative.
Interchanging the time derivative with the spatial integral is intentionally left as a separate
analytic step, so no hidden dominated-convergence hypothesis is introduced.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- Probability density smeared against a real spatial test function on an interval. -/
def intervalSmearedProbabilityDensity1D
    (a b : ℝ) (test : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∫ x in a..b, test x * probabilityDensityValue (ψ x)

/-- Spatially smeared value of the pointwise density time derivative. -/
def intervalSmearedDensityRate1D
    (a b : ℝ) (test densityTimeDerivative : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, test x * densityTimeDerivative x

/-- Pairing of the spatial derivative of a test function with the probability current. -/
def intervalSmearedCurrentPairing1D
    (a b : ℝ) (testDerivative current : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, testDerivative x * current x

/-- Weighted probability-current contribution at the two endpoints of an interval. -/
def weightedBoundaryCurrent1D
    (a b : ℝ) (test current : ℝ → ℝ) : ℝ :=
  test b * current b - test a * current a

/-- A pointwise one-dimensional continuity equation implies the interval weak balance.

The result is

`∫ test * ρₜ = ∫ test' * j - (test(b) j(b) - test(a) j(a))`.

The derivative and interval-integrability assumptions are exactly those needed for Mathlib's
integration-by-parts theorem. -/
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
  have hpointwiseIntegral :
      (∫ x in a..b, test x * densityTimeDerivative x) =
        -(∫ x in a..b, test x * currentDerivative x) := by
    calc
      (∫ x in a..b, test x * densityTimeDerivative x) =
          ∫ x in a..b, -(test x * currentDerivative x) := by
            apply intervalIntegral.integral_congr_ae
            exact Filter.Eventually.of_forall fun x _ => by
              have hx := hcontinuity x
              have hdensity : densityTimeDerivative x = -currentDerivative x := by
                linarith
              rw [hdensity]
              ring
      _ = -(∫ x in a..b, test x * currentDerivative x) := by
        rw [intervalIntegral.integral_neg]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    htest hcurrent htestIntegrable hcurrentIntegrable
  unfold intervalSmearedDensityRate1D intervalSmearedCurrentPairing1D
    weightedBoundaryCurrent1D
  rw [hpointwiseIntegral, hparts]
  ring

/-- Weak continuity with no boundary term for a test function vanishing at both endpoints. -/
theorem weak_continuity_interval_of_pointwise_zero_boundary
    (a b : ℝ)
    {test testDerivative current currentDerivative densityTimeDerivative : ℝ → ℝ}
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable currentDerivative volume a b)
    (ha : test a = 0) (hb : test b = 0) :
    intervalSmearedDensityRate1D a b test densityTimeDerivative =
      intervalSmearedCurrentPairing1D a b testDerivative current := by
  rw [weak_continuity_interval_of_pointwise a b hcontinuity htest hcurrent
    htestIntegrable hcurrentIntegrable]
  simp [weightedBoundaryCurrent1D, ha, hb]

/-- The scalar-potential Schrödinger equation gives the one-dimensional interval weak balance.

The wavefunction derivative hypotheses are stated coordinatewise, as in the pointwise continuity
kernel. `hcurrentIntegrable` is the remaining spatial integrability assumption needed for integration
by parts. -/
theorem schrodinger_weak_continuity_interval
    (a b ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {test testDerivative : ℝ → ℝ}
    {ψ ψx ψt ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
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
  apply weak_continuity_interval_of_pointwise a b
  · intro x
    exact probability_continuity_balance_of_schrodinger
      ℏ κ (potential x) (ψ x) (ψt x) (ψxx x) hℏ (hschrodinger x)
  · exact htest
  · intro x hx
    exact hasDerivAt_probabilityCurrentValue1D ℏ κ
      (hψre x hx) (hψim x hx) (hψxre x hx) (hψxim x hx)
  · exact htestIntegrable
  · exact hcurrentIntegrable

/-- Schrödinger weak continuity for test functions vanishing at the interval endpoints. -/
theorem schrodinger_weak_continuity_interval_zero_boundary
    (a b ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {test testDerivative : ℝ → ℝ}
    {ψ ψx ψt ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
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

end
end Continuum
end SingleParticle
end QuantumMechanics
