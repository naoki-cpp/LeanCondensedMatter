import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuitySmeared1D
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

/-- Probability density smeared over all of one-dimensional space. -/
def wholeSpaceSmearedProbabilityDensity1D
    (test : ℝ → ℝ) (ψ : ℝ → ℂ) : ℝ :=
  ∫ x, test x * probabilityDensityValue (ψ x)

/-- Whole-space pairing of a test function with a pointwise density time derivative. -/
def wholeSpaceSmearedDensityRate1D
    (test densityTimeDerivative : ℝ → ℝ) : ℝ :=
  ∫ x, test x * densityTimeDerivative x

/-- Whole-space pairing of the derivative of a test function with a probability current. -/
def wholeSpaceSmearedCurrentPairing1D
    (testDerivative current : ℝ → ℝ) : ℝ :=
  ∫ x, testDerivative x * current x

private theorem support_mul_right_of_tsupport_subset_Ioo
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    Function.support (fun x => f x * g x) ⊆ Ioc a b := by
  intro x hx
  have hfx : f x ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  have hxTop : x ∈ tsupport f := by
    exact subset_closure hfx
  have hxab := hf hxTop
  exact ⟨hxab.1, hxab.2.le⟩

private theorem support_deriv_mul_right_of_tsupport_subset_Ioo
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    Function.support (fun x => deriv f x * g x) ⊆ Ioc a b := by
  intro x hx
  have hdx : deriv f x ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  have hxTop : x ∈ tsupport f := by
    exact support_deriv_subset hdx
  have hxab := hf hxTop
  exact ⟨hxab.1, hxab.2.le⟩

private theorem endpoint_values_eq_zero_of_tsupport_subset_Ioo
    {a b : ℝ} {f : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo a b) :
    f a = 0 ∧ f b = 0 := by
  constructor
  · by_contra ha
    have haTop : a ∈ tsupport f := by
      exact subset_closure ha
    exact (lt_irrefl a (hf haTop).1)
  · by_contra hb
    have hbTop : b ∈ tsupport f := by
      exact subset_closure hb
    exact (lt_irrefl b (hf hbTop).2)

/-- If the test support is strictly inside `a..b`, its interval-smeared density is the whole-space
smeared density. -/
theorem intervalSmearedProbabilityDensity1D_eq_wholeSpace
    (a b : ℝ) {test : ℝ → ℝ} {ψ : ℝ → ℂ}
    (htestSupport : tsupport test ⊆ Ioo a b) :
    intervalSmearedProbabilityDensity1D a b test ψ =
      wholeSpaceSmearedProbabilityDensity1D test ψ := by
  unfold intervalSmearedProbabilityDensity1D wholeSpaceSmearedProbabilityDensity1D
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (support_mul_right_of_tsupport_subset_Ioo htestSupport)

/-- If the test support is strictly inside `a..b`, the interval density-rate pairing is the
corresponding whole-space pairing. -/
theorem intervalSmearedDensityRate1D_eq_wholeSpace
    (a b : ℝ) {test densityTimeDerivative : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b) :
    intervalSmearedDensityRate1D a b test densityTimeDerivative =
      wholeSpaceSmearedDensityRate1D test densityTimeDerivative := by
  unfold intervalSmearedDensityRate1D wholeSpaceSmearedDensityRate1D
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (support_mul_right_of_tsupport_subset_Ioo htestSupport)

/-- The interval pairing with `deriv test` agrees with the whole-space pairing whenever the
support of `test` lies strictly inside the interval. -/
theorem intervalSmearedCurrentPairing1D_deriv_eq_wholeSpace
    (a b : ℝ) {test current : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b) :
    intervalSmearedCurrentPairing1D a b (deriv test) current =
      wholeSpaceSmearedCurrentPairing1D (deriv test) current := by
  unfold intervalSmearedCurrentPairing1D wholeSpaceSmearedCurrentPairing1D
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (support_deriv_mul_right_of_tsupport_subset_Ioo htestSupport)

/-- A pointwise continuity equation gives the standard whole-space weak identity against a
differentiable test function supported strictly inside a finite interval.

The finite support window is only an analytic device for applying the previously established interval
integration-by-parts theorem. The conclusion itself contains only integrals over all of `ℝ`. -/
theorem weak_continuity_wholeSpace_of_pointwise
    (a b : ℝ)
    {test current currentDerivative densityTimeDerivative : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (htestDifferentiable : Differentiable ℝ test)
    (hcontinuity : ∀ x, densityTimeDerivative x + currentDerivative x = 0)
    (hcurrent : ∀ x ∈ [[a, b]], HasDerivAt current (currentDerivative x) x)
    (htestDerivIntegrable : IntervalIntegrable (deriv test) volume a b)
    (hcurrentIntegrable : IntervalIntegrable currentDerivative volume a b) :
    wholeSpaceSmearedDensityRate1D test densityTimeDerivative =
      wholeSpaceSmearedCurrentPairing1D (deriv test) current := by
  have htest : ∀ x ∈ [[a, b]], HasDerivAt test (deriv test x) x := by
    intro x _
    exact (htestDifferentiable x).hasDerivAt
  rcases endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
  have hweak := weak_continuity_interval_of_pointwise_zero_boundary
    a b hcontinuity htest hcurrent htestDerivIntegrable hcurrentIntegrable ha hb
  rw [intervalSmearedDensityRate1D_eq_wholeSpace a b htestSupport,
    intervalSmearedCurrentPairing1D_deriv_eq_wholeSpace a b htestSupport] at hweak
  exact hweak

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
  apply weak_continuity_wholeSpace_of_pointwise a b htestSupport htestDifferentiable
  · intro x
    exact probability_continuity_balance_of_schrodinger
      ℏ κ (potential x) (ψ x) (ψt x) (ψxx x) hℏ (hschrodinger x)
  · intro x hx
    exact hasDerivAt_probabilityCurrentValue1D ℏ κ
      (hψre x hx) (hψim x hx) (hψxre x hx) (hψxim x hx)
  · exact htestDerivIntegrable
  · exact hcurrentIntegrable

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
  have htest : ∀ x ∈ [[a, b]], HasDerivAt test (deriv test x) x := by
    intro x _
    exact (htestDifferentiable x).hasDerivAt
  have hInterval := hasDerivAt_intervalSmearedProbabilityDensity1D_of_schrodinger
    a b t ℏ κ hℏ hs hDensityMeas hDensityIntegrable hDensityRateMeas hBound
      hBoundIntegrable htimeRe htimeIm htest hψre hψim hψxre hψxim hschrodinger
      htestDerivIntegrable hcurrentIntegrable
  have hDensityWindow :
      (fun τ => intervalSmearedProbabilityDensity1D a b test (ψ τ)) =
        fun τ => wholeSpaceSmearedProbabilityDensity1D test (ψ τ) := by
    funext τ
    exact intervalSmearedProbabilityDensity1D_eq_wholeSpace a b htestSupport
  have hCurrentWindow :
      intervalSmearedCurrentPairing1D a b (deriv test)
          (fun x => probabilityCurrentValue1D ℏ κ (ψ t x) (ψx x)) =
        wholeSpaceSmearedCurrentPairing1D (deriv test)
          (fun x => probabilityCurrentValue1D ℏ κ (ψ t x) (ψx x)) :=
    intervalSmearedCurrentPairing1D_deriv_eq_wholeSpace a b htestSupport
  have hBoundary :
      weightedBoundaryCurrent1D a b test
          (fun x => probabilityCurrentValue1D ℏ κ (ψ t x) (ψx x)) = 0 := by
    rcases endpoint_values_eq_zero_of_tsupport_subset_Ioo htestSupport with ⟨ha, hb⟩
    simp [weightedBoundaryCurrent1D, ha, hb]
  rw [hDensityWindow, hCurrentWindow, hBoundary, sub_zero] at hInterval
  exact hInterval

end
end Continuum
end SingleParticle
end QuantumMechanics
