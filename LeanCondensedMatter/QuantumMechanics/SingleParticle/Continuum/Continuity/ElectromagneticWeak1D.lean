import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Electromagnetic1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.CompactSupport1D
import LeanCondensedMatter.Analysis.ConservationLaw.WeakConservation1D
import Mathlib.Tactic.Module

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
    (hψ : ∀ x ∈ [[a, b]], HasDerivAt ψ (ψx x) x)
    (hψx : ∀ x ∈ [[a, b]], HasDerivAt ψx (ψxx x) x)
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
    (∫ x in a..b, test x * probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      (∫ x in a..b, testDerivative x * electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ x) (ψx x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ x) (ψx x)) := by
  have hcurrent : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => electromagneticProbabilityCurrentValue1D
        q ℏ mass (vectorPotential y) (ψ y) (ψx y))
        (electromagneticProbabilityCurrentDivergenceValue1D
          q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
          (ψ x) (ψx x) (ψxx x)) x := by
    intro x hx
    exact hasDerivAt_electromagneticProbabilityCurrentValue1D
      q ℏ mass hℏ hmass (hA x hx) (hψ x hx)
      (hψx x hx)
  have hweak := ConservationLaw.weak_continuity_interval_of_pointwise
    (ContinuousLinearMap.mul ℝ ℝ) (a := a) (b := b)
    (test := test) (testDerivative := testDerivative)
    (current := fun x => electromagneticProbabilityCurrentValue1D
      q ℏ mass (vectorPotential x) (ψ x) (ψx x))
    (currentDerivative := fun x => electromagneticProbabilityCurrentDivergenceValue1D
      q ℏ mass (vectorPotential x) (vectorPotentialDerivative x)
      (ψ x) (ψx x) (ψxx x))
    (densityTimeDerivative := fun x => probabilityDensityTimeDerivativeValue (ψ x) (ψt x))
    (fun x => electromagnetic_probability_continuity_balance_of_schrodinger
      q ℏ mass (vectorPotential x) (vectorPotentialDerivative x) (scalarPotential x)
      (ψ x) (ψt x) (ψx x) (ψxx x) hℏ hmass (hschrodinger x))
    htest hcurrent
    (htestIntegrable.mul_continuousOn (HasDerivAt.continuousOn hcurrent))
    (hcurrentIntegrable.continuousOn_mul (HasDerivAt.continuousOn htest))
  simpa only [weightedBoundaryCurrent1D, ContinuousLinearMap.mul_apply'] using hweak

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
    (htime : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      HasDerivAt (fun u => ψ u x) (ψt τ x) τ)
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hψ : ∀ x ∈ [[a, b]], HasDerivAt (ψ t) (ψx x) x)
    (hψx : ∀ x ∈ [[a, b]], HasDerivAt ψx (ψxx x) x)
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
      ((∫ x in a..b, testDerivative x * electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ t x) (ψx x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => electromagneticProbabilityCurrentValue1D
            q ℏ mass (vectorPotential x) (ψ t x) (ψx x))) t := by
  have hdensity := hasDerivAt_intervalSmearedProbabilityDensity1D
    a b t hs hDensityMeas hDensityIntegrable hDensityRateMeas hBound hBoundIntegrable
      htime
  have hweak := electromagnetic_schrodinger_weak_continuity_interval
    a b q ℏ mass hℏ hmass htest hA hψ hψx hschrodinger
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
    (hψ : ∀ x ∈ [[a, b]], HasDerivAt ψ (ψx x) x)
    (hψx : ∀ x ∈ [[a, b]], HasDerivAt ψx (ψxx x) x)
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
    (∫ x, test x * probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
    (∫ x, deriv test x * electromagneticProbabilityCurrentValue1D
          q ℏ mass (vectorPotential x) (ψ x) (ψx x)) := by
  have hInterval := electromagnetic_schrodinger_weak_continuity_interval
    a b q ℏ mass hℏ hmass (fun x _ => (htestDifferentiable x).hasDerivAt)
      hA hψ hψx hschrodinger htestDerivIntegrable hcurrentIntegrable
  exact ConservationLaw.weak_continuity_wholeSpace_of_interval
    (ContinuousLinearMap.mul ℝ ℝ) a b htestSupport hInterval

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
    (htime : ∀ x ∈ uIoc a b, ∀ τ ∈ s,
      HasDerivAt (fun u => ψ u x) (ψt τ x) τ)
    (hA : ∀ x ∈ [[a, b]],
      HasDerivAt vectorPotential (vectorPotentialDerivative x) x)
    (hψ : ∀ x ∈ [[a, b]], HasDerivAt (ψ t) (ψx x) x)
    (hψx : ∀ x ∈ [[a, b]], HasDerivAt ψx (ψxx x) x)
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
      ((∫ x, deriv test x * electromagneticProbabilityCurrentValue1D
          q ℏ mass (vectorPotential x) (ψ t x) (ψx x))) t := by
  have hInterval :=
    hasDerivAt_intervalSmearedProbabilityDensity1D_of_electromagnetic_schrodinger
      a b t q ℏ mass hℏ hmass hs hDensityMeas hDensityIntegrable hDensityRateMeas
      hBound hBoundIntegrable htime
      (fun x _ => (htestDifferentiable x).hasDerivAt)
      hA hψ hψx hschrodinger htestDerivIntegrable hcurrentIntegrable
  exact hasDerivAt_wholeSpaceSmearedProbabilityDensity1D_of_interval
    a b t htestSupport hInterval

end
end Continuum
end SingleParticle
end QuantumMechanics
