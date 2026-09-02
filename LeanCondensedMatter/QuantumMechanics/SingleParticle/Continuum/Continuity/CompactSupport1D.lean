import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Smeared1D
import LeanCondensedMatter.Analysis.Calculus.WeakConservation1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Integral1D
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Compactly supported whole-space Schrödinger continuity in one dimension

This module turns the interval weak and smeared continuity theorems into whole-space statements for
a test function whose topological support lies strictly inside a finite interval. The strict support
window makes both endpoint values vanish and lets Mathlib's interval-integral support theorem identify
the interval pairings with their integrals over all of `ℝ`.

The time-differentiation hypotheses remain the explicit dominated-convergence assumptions from the
preceding smeared layer. No `L²` Hamiltonian or unbounded-operator claim is introduced here.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- Whole-space pairing of a test function with a pointwise density time derivative. -/
def wholeSpaceSmearedDensityRate1D
    (test densityTimeDerivative : ℝ → ℝ) : ℝ :=
  ∫ x, test x * densityTimeDerivative x

/-- Pairing of the derivative of a test function with a probability current. -/
def wholeSpaceSmearedCurrentPairing1D
    (testDerivative current : ℝ → ℝ) : ℝ :=
  wholeSpaceSmearedDensityRate1D testDerivative current

/-- If the test support is strictly inside `a..b`, its interval-smeared density is the whole-space
smeared density. -/
theorem intervalSmearedProbabilityDensity1D_eq_wholeSpace
    (a b : ℝ) {test : ℝ → ℝ} {ψ : ℝ → ℂ}
    (htestSupport : tsupport test ⊆ Ioo a b) :
    intervalSmearedProbabilityDensity1D a b test ψ =
      wholeSpaceSmearedProbabilityDensity1D test ψ := by
  unfold intervalSmearedProbabilityDensity1D wholeSpaceSmearedProbabilityDensity1D
  exact ConservationLaw.integral_mul_eq_integral_of_tsupport_subset_Ioo htestSupport

/-- If the test support is strictly inside `a..b`, its interval pairing with a density rate is the
whole-space pairing. -/
theorem intervalSmearedDensityRate1D_eq_wholeSpace
    (a b : ℝ) {test densityTimeDerivative : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b) :
    intervalSmearedDensityRate1D a b test densityTimeDerivative =
      wholeSpaceSmearedDensityRate1D test densityTimeDerivative := by
  unfold intervalSmearedDensityRate1D wholeSpaceSmearedDensityRate1D
  exact ConservationLaw.integral_mul_eq_integral_of_tsupport_subset_Ioo htestSupport

/-- The interval pairing with `deriv test` agrees with the whole-space pairing whenever the
support of `test` lies strictly inside the interval. -/
theorem intervalSmearedCurrentPairing1D_deriv_eq_wholeSpace
    (a b : ℝ) {test current : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b) :
    intervalSmearedCurrentPairing1D a b (deriv test) current =
      wholeSpaceSmearedCurrentPairing1D (deriv test) current := by
  unfold intervalSmearedCurrentPairing1D wholeSpaceSmearedCurrentPairing1D
  unfold intervalSmearedDensityRate1D wholeSpaceSmearedDensityRate1D
  exact ConservationLaw.integral_deriv_mul_eq_integral_of_tsupport_subset_Ioo htestSupport

/-- A compact support window transports an interval weak balance to the corresponding whole-space
identity. -/
theorem weak_continuity_wholeSpace_of_interval
    (a b : ℝ) {test current densityTimeDerivative : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (hInterval :
      intervalSmearedDensityRate1D a b test densityTimeDerivative =
        intervalSmearedCurrentPairing1D a b (deriv test) current -
          weightedBoundaryCurrent1D a b test current) :
    wholeSpaceSmearedDensityRate1D test densityTimeDerivative =
      wholeSpaceSmearedCurrentPairing1D (deriv test) current := by
  have hDensityWindow :
      intervalSmearedDensityRate1D a b test densityTimeDerivative =
        wholeSpaceSmearedDensityRate1D test densityTimeDerivative :=
    intervalSmearedDensityRate1D_eq_wholeSpace a b htestSupport
  have hCurrentWindow :
      intervalSmearedCurrentPairing1D a b (deriv test) current =
        wholeSpaceSmearedCurrentPairing1D (deriv test) current :=
    intervalSmearedCurrentPairing1D_deriv_eq_wholeSpace a b htestSupport
  rcases ConservationLaw.endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
  have hBoundary : weightedBoundaryCurrent1D a b test current = 0 := by
    simp [weightedBoundaryCurrent1D, ha, hb]
  rw [hDensityWindow, hCurrentWindow, hBoundary, sub_zero] at hInterval
  exact hInterval

/-- A compact support window transports an interval smeared-density derivative theorem to the
corresponding whole-space statement. -/
theorem hasDerivAt_wholeSpaceSmearedProbabilityDensity1D_of_interval
    (a b t : ℝ)
    {test : ℝ → ℝ} {ψ : ℝ → ℝ → ℂ} {current : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (hInterval : HasDerivAt
      (fun τ => intervalSmearedProbabilityDensity1D a b test (ψ τ))
      (intervalSmearedCurrentPairing1D a b (deriv test) current -
        weightedBoundaryCurrent1D a b test current) t) :
    HasDerivAt
      (fun τ => wholeSpaceSmearedProbabilityDensity1D test (ψ τ))
      (wholeSpaceSmearedCurrentPairing1D (deriv test) current) t := by
  have hDensityWindow :
      (fun τ => intervalSmearedProbabilityDensity1D a b test (ψ τ)) =
        fun τ => wholeSpaceSmearedProbabilityDensity1D test (ψ τ) := by
    funext τ
    exact intervalSmearedProbabilityDensity1D_eq_wholeSpace a b htestSupport
  have hCurrentWindow :
      intervalSmearedCurrentPairing1D a b (deriv test) current =
        wholeSpaceSmearedCurrentPairing1D (deriv test) current :=
    intervalSmearedCurrentPairing1D_deriv_eq_wholeSpace a b htestSupport
  rcases ConservationLaw.endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
  have hBoundary : weightedBoundaryCurrent1D a b test current = 0 := by
    simp [weightedBoundaryCurrent1D, ha, hb]
  rw [hDensityWindow, hCurrentWindow, hBoundary, sub_zero] at hInterval
  exact hInterval

/-- The scalar-potential Schrödinger equation gives the whole-space weak continuity identity against
a differentiable compactly supported test function. -/
theorem schrodinger_weak_continuity_wholeSpace
    (a b ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {test : ℝ → ℝ} {ψ ψx ψt ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (htestDifferentiable : Differentiable ℝ test)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        -(κ : ℂ) * ψxx x + (potential x : ℂ) * ψ x)
    (htestDerivIntegrable : IntervalIntegrable (deriv test) volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D ℏ κ (ψ x) (ψxx x)) volume a b) :
    wholeSpaceSmearedDensityRate1D test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      wholeSpaceSmearedCurrentPairing1D (deriv test)
        (fun x => probabilityCurrentValue1D ℏ κ (ψ x) (ψx x)) := by
  have hInterval := schrodinger_weak_continuity_interval
    a b ℏ κ hℏ (fun x _ => (htestDifferentiable x).hasDerivAt)
      hψre hψim hψxre hψxim hschrodinger htestDerivIntegrable hcurrentIntegrable
  exact weak_continuity_wholeSpace_of_interval a b htestSupport hInterval

/-- Under the explicit dominated time-differentiation hypotheses, the scalar-potential Schrödinger
equation gives the derivative of the whole-space compactly supported smeared density:

`d/dt ∫ test * ρ = ∫ (deriv test) * j`.

The support condition is stated as `tsupport test ⊆ Ioo a b`, making the compact support window and
the disappearance of the boundary current explicit at the theorem boundary. -/
theorem hasDerivAt_wholeSpaceSmearedProbabilityDensity1D_of_schrodinger
    (a b t ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {s : Set ℝ} {bound test : ℝ → ℝ}
    {ψ ψt : ℝ → ℝ → ℂ} {ψx ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (htestDifferentiable : Differentiable ℝ test)
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
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt t x =
        -(κ : ℂ) * ψxx x + (potential x : ℂ) * ψ t x)
    (htestDerivIntegrable : IntervalIntegrable (deriv test) volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D ℏ κ (ψ t x) (ψxx x)) volume a b) :
    HasDerivAt
      (fun τ => wholeSpaceSmearedProbabilityDensity1D test (ψ τ))
      (wholeSpaceSmearedCurrentPairing1D (deriv test)
        (fun x => probabilityCurrentValue1D ℏ κ (ψ t x) (ψx x))) t := by
  have hInterval := hasDerivAt_intervalSmearedProbabilityDensity1D_of_schrodinger
    a b t ℏ κ hℏ hs hDensityMeas hDensityIntegrable hDensityRateMeas hBound
      hBoundIntegrable htimeRe htimeIm (fun x _ => (htestDifferentiable x).hasDerivAt)
      hψre hψim hψxre hψxim hschrodinger htestDerivIntegrable hcurrentIntegrable
  exact hasDerivAt_wholeSpaceSmearedProbabilityDensity1D_of_interval
    a b t htestSupport hInterval

end
end Continuum
end SingleParticle
end QuantumMechanics
