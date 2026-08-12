import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerGaugeContinuity1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuityCompactSupport1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuitySchwartz1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak and smeared gauge-covariant Schrödinger continuity in one dimension

This module connects the pointwise electromagnetic continuity equation to the generic weak,
time-smeared, and compact-support whole-space machinery developed for the scalar-potential theory.
The vector potential and its spatial derivative remain explicit inputs, so no smoothness assumption is
hidden in the current notation.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- The minimally coupled Schrödinger equation gives the interval weak probability balance. -/
theorem electromagnetic_schrodinger_weak_continuity_interval
    (a b q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {test testDerivative vectorPotential vectorPotentialDerivative : ℝ → ℝ}
    {ψ ψx ψt ψxx : ℝ → ℂ} {scalarPotential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
          (ψ x) (ψx x) (ψxx x))
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
        (ψ x) (ψx x) (ψxx x)) volume a b) :
    intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      intervalSmearedCurrentPairing1D a b testDerivative
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ x) (ψx x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ x) (ψx x)) := by
  apply weak_continuity_interval_of_pointwise a b
  · intro x
    exact electromagnetic_probability_continuity_balance_of_schrodinger
      q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
      (ψ x) (ψt x) (ψx x) (ψxx x) hℏ hmass (hschrodinger x)
  · exact htest
  · intro x hx
    exact hasDerivAt_electromagneticProbabilityCurrentValue1D
      q ℏ mass hℏ hmass (hA x hx) (hψre x hx) (hψim x hx)
      (hψxre x hx) (hψxim x hx)
  · exact htestIntegrable
  · exact hcurrentIntegrable

/-- Electromagnetic interval weak continuity when the test function vanishes at both endpoints. -/
theorem electromagnetic_schrodinger_weak_continuity_interval_zero_boundary
    (a b q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {test testDerivative vectorPotential vectorPotentialDerivative : ℝ → ℝ}
    {ψ ψx ψt ψxx : ℝ → ℂ} {scalarPotential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
          (ψ x) (ψx x) (ψxx x))
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
        (ψ x) (ψx x) (ψxx x)) volume a b)
    (ha : test a = 0) (hb : test b = 0) :
    intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      intervalSmearedCurrentPairing1D a b testDerivative
        (fun x => electromagneticProbabilityCurrentValue1D
          q ℏ mass (vectorPotential x) (ψ x) (ψx x)) := by
  rw [electromagnetic_schrodinger_weak_continuity_interval
    a b q ℏ mass hℏ hmass htest hA hψre hψim hψxre hψxim hschrodinger
    htestIntegrable hcurrentIntegrable]
  simp [weightedBoundaryCurrent1D, ha, hb]

/-- Under explicit dominated time-differentiation hypotheses, the electromagnetic Schrödinger
 equation gives the derivative of an interval-smeared probability density. -/
theorem hasDerivAt_intervalSmearedProbabilityDensity1D_of_electromagnetic_schrodinger
    (a b t q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {s : Set ℝ} {bound test testDerivative vectorPotential vectorPotentialDerivative : ℝ → ℝ}
    {ψ ψt : ℝ → ℝ → ℂ} {ψx ψxx : ℝ → ℂ} {scalarPotential : ℝ → ℝ}
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
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt t x =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
          (ψ t x) (ψx x) (ψxx x))
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
        (ψ t x) (ψx x) (ψxx x)) volume a b) :
    HasDerivAt
      (fun τ => intervalSmearedProbabilityDensity1D a b test (ψ τ))
      (intervalSmearedCurrentPairing1D a b testDerivative
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ t x) (ψx x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ t x) (ψx x))) t := by
  have hdensity := hasDerivAt_intervalSmearedProbabilityDensity1D
    a b t hs hDensityMeas hDensityIntegrable hDensityRateMeas hBound hBoundIntegrable
      htimeRe htimeIm
  have hweak := electromagnetic_schrodinger_weak_continuity_interval
    a b q ℏ mass hℏ hmass htest hA hψre hψim hψxre hψxim hschrodinger
      htestIntegrable hcurrentIntegrable
  rw [hweak] at hdensity
  exact hdensity

/-- The electromagnetic Schrödinger equation gives whole-space weak continuity against a compactly
supported differentiable test function. -/
theorem electromagnetic_schrodinger_weak_continuity_wholeSpace
    (a b q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {test vectorPotential vectorPotentialDerivative : ℝ → ℝ}
    {ψ ψx ψt ψxx : ℝ → ℂ} {scalarPotential : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (htestDifferentiable : Differentiable ℝ test)
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
          (ψ x) (ψx x) (ψxx x))
    (htestDerivIntegrable : IntervalIntegrable (deriv test) volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
        (ψ x) (ψx x) (ψxx x)) volume a b) :
    wholeSpaceSmearedDensityRate1D test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      wholeSpaceSmearedCurrentPairing1D (deriv test)
        (fun x => electromagneticProbabilityCurrentValue1D
          q ℏ mass (vectorPotential x) (ψ x) (ψx x)) := by
  apply weak_continuity_wholeSpace_of_pointwise a b htestSupport htestDifferentiable
  · intro x
    exact electromagnetic_probability_continuity_balance_of_schrodinger
      q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
      (ψ x) (ψt x) (ψx x) (ψxx x) hℏ hmass (hschrodinger x)
  · intro x hx
    exact hasDerivAt_electromagneticProbabilityCurrentValue1D
      q ℏ mass hℏ hmass (hA x hx) (hψre x hx) (hψim x hx)
      (hψxre x hx) (hψxim x hx)
  · exact htestDerivIntegrable
  · exact hcurrentIntegrable

/-- Under the existing dominated time-differentiation hypotheses, the electromagnetic equation gives
`d/dt ∫ test ρ = ∫ test' j` for a compactly supported spatial test function. -/
theorem hasDerivAt_wholeSpaceSmearedProbabilityDensity1D_of_electromagnetic_schrodinger
    (a b t q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {s : Set ℝ} {bound test vectorPotential vectorPotentialDerivative : ℝ → ℝ}
    {ψ ψt : ℝ → ℝ → ℂ} {ψx ψxx : ℝ → ℂ} {scalarPotential : ℝ → ℝ}
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
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hψre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).re) (ψx x).re x)
    (hψim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψ t y).im) (ψx x).im x)
    (hψxre : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).re) (ψxx x).re x)
    (hψxim : ∀ x ∈ [[a, b]], HasDerivAt (fun y => (ψx y).im) (ψxx x).im x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt t x =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
          (ψ t x) (ψx x) (ψxx x))
    (htestDerivIntegrable : IntervalIntegrable (deriv test) volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
        (ψ t x) (ψx x) (ψxx x)) volume a b) :
    HasDerivAt
      (fun τ => wholeSpaceSmearedProbabilityDensity1D test (ψ τ))
      (wholeSpaceSmearedCurrentPairing1D (deriv test)
        (fun x => electromagneticProbabilityCurrentValue1D
          q ℏ mass (vectorPotential x) (ψ t x) (ψx x))) t := by
  have htest : ∀ x ∈ [[a, b]], HasDerivAt test (deriv test x) x := by
    intro x _
    exact (htestDifferentiable x).hasDerivAt
  have hInterval :=
    hasDerivAt_intervalSmearedProbabilityDensity1D_of_electromagnetic_schrodinger
      a b t q ℏ mass hℏ hmass hs hDensityMeas hDensityIntegrable hDensityRateMeas
      hBound hBoundIntegrable htimeRe htimeIm htest hA hψre hψim hψxre hψxim
      hschrodinger htestDerivIntegrable hcurrentIntegrable
  have hDensityWindow :
      (fun τ => intervalSmearedProbabilityDensity1D a b test (ψ τ)) =
        fun τ => wholeSpaceSmearedProbabilityDensity1D test (ψ τ) := by
    funext τ
    exact intervalSmearedProbabilityDensity1D_eq_wholeSpace a b htestSupport
  have hCurrentWindow :
      intervalSmearedCurrentPairing1D a b (deriv test)
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ t x) (ψx x)) =
        wholeSpaceSmearedCurrentPairing1D (deriv test)
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ t x) (ψx x)) :=
    intervalSmearedCurrentPairing1D_deriv_eq_wholeSpace a b htestSupport
  have hBoundary :
      weightedBoundaryCurrent1D a b test
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ t x) (ψx x)) = 0 := by
    have hweak := weak_continuity_wholeSpace_of_pointwise
    rcases Classical.em (test a = 0) with ha | ha
    · have hb : test b = 0 := by
        by_contra hb
        have hbTop : b ∈ tsupport test := subset_closure hb
        exact (lt_irrefl b (htestSupport hbTop).2)
      simp [weightedBoundaryCurrent1D, ha, hb]
    · have haTop : a ∈ tsupport test := subset_closure ha
      exact (False.elim (lt_irrefl a (htestSupport haTop).1))
  rw [hDensityWindow, hCurrentWindow, hBoundary, sub_zero] at hInterval
  exact hInterval

/-- For a Schwartz spatial wavefunction, all wavefunction spatial differentiability hypotheses in
the electromagnetic interval weak theorem are automatic. -/
theorem electromagnetic_schrodinger_weak_continuity_interval_of_schwartz
    (a b q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {test testDerivative vectorPotential vectorPotentialDerivative : ℝ → ℝ}
    (ψ : SchwartzMap ℝ ℂ) {ψt : ℝ → ℂ} {scalarPotential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
          (ψ x) (schwartzSpatialDerivative1D ψ x) (schwartzSpatialSecondDerivative1D ψ x))
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
        (ψ x) (schwartzSpatialDerivative1D ψ x) (schwartzSpatialSecondDerivative1D ψ x))
      volume a b) :
    intervalSmearedDensityRate1D a b test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      intervalSmearedCurrentPairing1D a b testDerivative
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ x) (schwartzSpatialDerivative1D ψ x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ x) (schwartzSpatialDerivative1D ψ x)) := by
  apply electromagnetic_schrodinger_weak_continuity_interval
    a b q ℏ mass hℏ hmass htest hA
  · intro x _
    exact hasDerivAt_schwartzSpatialDerivative1D_re ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialDerivative1D_im ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialSecondDerivative1D_re ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialSecondDerivative1D_im ψ x
  · exact hschrodinger
  · exact htestIntegrable
  · exact hcurrentIntegrable

/-- Compact-support whole-space weak electromagnetic continuity for a Schwartz spatial wavefunction. -/
theorem electromagnetic_schrodinger_weak_continuity_wholeSpace_of_schwartz
    (a b q ℏ mass : ℝ) (hℏ : ℏ ≠ 0) (hmass : mass ≠ 0)
    {test vectorPotential vectorPotentialDerivative : ℝ → ℝ}
    (ψ : SchwartzMap ℝ ℂ) {ψt : ℝ → ℂ} {scalarPotential : ℝ → ℝ}
    (htestSupport : tsupport test ⊆ Ioo a b)
    (htestDifferentiable : Differentiable ℝ test)
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        minimallyCoupledSchrodingerRhsValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
          (ψ x) (schwartzSpatialDerivative1D ψ x) (schwartzSpatialSecondDerivative1D ψ x))
    (htestDerivIntegrable : IntervalIntegrable (deriv test) volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => electromagneticProbabilityCurrentDivergenceValue1D
        q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
        (ψ x) (schwartzSpatialDerivative1D ψ x) (schwartzSpatialSecondDerivative1D ψ x))
      volume a b) :
    wholeSpaceSmearedDensityRate1D test
        (fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      wholeSpaceSmearedCurrentPairing1D (deriv test)
        (fun x => electromagneticProbabilityCurrentValue1D
          q ℏ mass (vectorPotential x) (ψ x) (schwartzSpatialDerivative1D ψ x)) := by
  apply electromagnetic_schrodinger_weak_continuity_wholeSpace
    a b q ℏ mass hℏ hmass htestSupport htestDifferentiable hA
  · intro x _
    exact hasDerivAt_schwartzSpatialDerivative1D_re ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialDerivative1D_im ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialSecondDerivative1D_re ψ x
  · intro x _
    exact hasDerivAt_schwartzSpatialSecondDerivative1D_im ψ x
  · exact hschrodinger
  · exact htestDerivIntegrable
  · exact hcurrentIntegrable

end
end Continuum
end SingleParticle
end QuantumMechanics
