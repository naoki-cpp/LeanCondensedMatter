import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuityWeak1D
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Time-dependent smeared one-dimensional Schrödinger continuity

This module completes the next analytic step after the interval weak balance: under explicit local
dominated-derivative hypotheses, the time derivative can be moved through the spatial interval
integral defining a smeared probability density. Combining that differentiation theorem with the
existing weak Schrödinger continuity equation gives a genuine time-derivative statement for the
smeared density.

The domination, measurability, and interval-integrability assumptions are kept visible. No `L²`
Hamiltonian, Sobolev-domain, or unbounded-operator assertion is introduced here.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- Differentiate a spatially smeared probability density with respect to time.

The time-dependent wavefunction is `ψ : ℝ → ℝ → ℂ`, with `ψt` supplying its pointwise time
derivative. The hypotheses expose exactly the local domination and measurability conditions needed
by Mathlib's parametric interval-integral theorem. -/
theorem hasDerivAt_intervalSmearedProbabilityDensity1D
    (a b t : ℝ)
    {s : Set ℝ} {bound test : ℝ → ℝ}
    {ψ ψt : ℝ → ℝ → ℂ}
    (hs : s ∈ nhds t)
    (hDensityMeas : ∀ τ ∈ s,
      AEStronglyMeasurable
        (fun x => test x * probabilityDensityValue (ψ τ x))
        (volume.restrict (uIoc a b)))
    (hDensityIntegrable : IntervalIntegrable
      (fun x => test x * probabilityDensityValue (ψ t x)) volume a b)
    (hDensityRateMeas : AEStronglyMeasurable
      (fun x => test x * probabilityDensityTimeDerivativeValue (ψ t x) (ψt t x))
      (volume.restrict (uIoc a b)))
    (hBound : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      ‖test x * probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)‖ ≤ bound x)
    (hBoundIntegrable : IntervalIntegrable bound volume a b)
    (htimeRe : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).re) (ψt τ x).re τ)
    (htimeIm : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).im) (ψt τ x).im τ) :
    HasDerivAt
      (fun τ => intervalSmearedProbabilityDensity1D a b test (ψ τ))
      (intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue (ψ t x) (ψt t x))) t := by
  have hFMeas : ∀ᶠ τ in nhds t,
      AEStronglyMeasurable
        (fun x => test x * probabilityDensityValue (ψ τ x))
        (volume.restrict (uIoc a b)) := by
    filter_upwards [hs] with τ hτ
    exact hDensityMeas τ hτ
  have hBoundAE : ∀ᵐ x ∂volume, x ∈ uIoc a b → ∀ τ ∈ s,
      ‖test x * probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)‖ ≤ bound x :=
    Filter.Eventually.of_forall fun x hx => hBound x hx
  have hDiff : ∀ᵐ x ∂volume, x ∈ uIoc a b → ∀ τ ∈ s,
      HasDerivAt
        (fun u => test x * probabilityDensityValue (ψ u x))
        (test x * probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)) τ :=
    Filter.Eventually.of_forall fun x hx τ hτ =>
      (hasDerivAt_probabilityDensityValue
        (htimeRe x hx τ hτ) (htimeIm x hx τ hτ)).const_mul (test x)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ x => test x * probabilityDensityValue (ψ τ x))
    (F' := fun τ x => test x * probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x))
    hs hFMeas hDensityIntegrable hDensityRateMeas hBoundAE hBoundIntegrable hDiff
  simpa [intervalSmearedProbabilityDensity1D, intervalSmearedDensityRate1D] using h.2

/-- The scalar-potential Schrödinger equation gives the time derivative of the spatially smeared
probability density.

The conclusion is

`d/dt ∫ test * ρ = ∫ test' * j - (test(b)j(b) - test(a)j(a))`.

Time differentiation under the integral uses the explicit dominated-derivative hypotheses above;
the spatial current term is supplied by the previously proved interval weak continuity theorem. -/
theorem hasDerivAt_intervalSmearedProbabilityDensity1D_of_schrodinger
    (a b t ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {s : Set ℝ} {bound test testDerivative : ℝ → ℝ}
    {ψ ψt : ℝ → ℝ → ℂ} {ψx ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (hs : s ∈ nhds t)
    (hDensityMeas : ∀ τ ∈ s,
      AEStronglyMeasurable
        (fun x => test x * probabilityDensityValue (ψ τ x))
        (volume.restrict (uIoc a b)))
    (hDensityIntegrable : IntervalIntegrable
      (fun x => test x * probabilityDensityValue (ψ t x)) volume a b)
    (hDensityRateMeas : AEStronglyMeasurable
      (fun x => test x * probabilityDensityTimeDerivativeValue (ψ t x) (ψt t x))
      (volume.restrict (uIoc a b)))
    (hBound : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      ‖test x * probabilityDensityTimeDerivativeValue (ψ τ x) (ψt τ x)‖ ≤ bound x)
    (hBoundIntegrable : IntervalIntegrable bound volume a b)
    (htimeRe : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).re) (ψt τ x).re τ)
    (htimeIm : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      HasDerivAt (fun u => (ψ u x).im) (ψt τ x).im τ)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt t x =
        -(κ : ℂ) * ψxx x + (potential x : ℂ) * ψ t x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D ℏ κ (ψ t x) (ψxx x)) volume a b) :
    HasDerivAt
      (fun τ => intervalSmearedProbabilityDensity1D a b test (ψ τ))
      (intervalSmearedCurrentPairing1D a b testDerivative
          (fun x => probabilityCurrentValue1D ℏ κ (ψ t x) (ψx x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => probabilityCurrentValue1D ℏ κ (ψ t x) (ψx x))) t := by
  have hdensity := hasDerivAt_intervalSmearedProbabilityDensity1D
    a b t hs hDensityMeas hDensityIntegrable hDensityRateMeas hBound hBoundIntegrable
      htimeRe htimeIm
  have hweak := schrodinger_weak_continuity_interval
    a b ℏ κ hℏ htest hψre hψim hψxre hψxim hschrodinger
      htestIntegrable hcurrentIntegrable
  rw [hweak] at hdensity
  exact hdensity

end
end Continuum
end SingleParticle
end QuantumMechanics
