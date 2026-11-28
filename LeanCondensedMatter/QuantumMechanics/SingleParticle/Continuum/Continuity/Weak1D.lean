import LeanCondensedMatter.Analysis.ConservationLaw.WeakConservation1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Probability.Integral1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.Scalar1D

set_option linter.style.header false

/-!
# Weak one-dimensional Schrödinger continuity equation

This module supplies the probability-density/current specializations of the generic
one-dimensional weak conservation-law kernel.  The integration-by-parts theorem itself lives under
`Analysis.ConservationLaw.WeakConservation1D` and is independent of quantum mechanics.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- Weighted probability-current contribution at the two endpoints of an interval. -/
def weightedBoundaryCurrent1D
    (a b : ℝ) (test current : ℝ → ℝ) : ℝ :=
  test b * current b - test a * current a

/-- The scalar-potential Schrödinger equation gives the one-dimensional interval weak balance.

The wavefunction derivative hypotheses are stated for complex-valued functions of a real variable. `hcurrentIntegrable` is the remaining spatial integrability assumption needed for
integration by parts.
-/
theorem schrodinger_weak_continuity_interval
    (a b ℏ κ : ℝ) (hℏ : ℏ ≠ 0)
    {test testDerivative : ℝ → ℝ}
    {ψ ψt ψx ψxx : ℝ → ℂ} {potential : ℝ → ℝ}
    (htest : ∀ x ∈ [[a, b]], HasDerivAt test (testDerivative x) x)
    (hψ : ∀ x ∈ [[a, b]],
      HasDerivAt ψ (ψx x) x)
    (hψx : ∀ x ∈ [[a, b]],
      HasDerivAt ψx (ψxx x) x)
    (hschrodinger : ∀ x,
      Complex.I * (ℏ : ℂ) * ψt x =
        -(κ : ℂ) * ψxx x + (potential x : ℂ) * ψ x)
    (htestIntegrable : IntervalIntegrable testDerivative volume a b)
    (hcurrentIntegrable : IntervalIntegrable
      (fun x => probabilityCurrentDivergenceValue1D ℏ κ (ψ x) (ψxx x)) volume a b) :
    (∫ x in a..b, test x * probabilityDensityTimeDerivativeValue (ψ x) (ψt x)) =
      (∫ x in a..b, testDerivative x * probabilityCurrentValue1D ℏ κ (ψ x) (ψx x)) -
        weightedBoundaryCurrent1D a b test
          (fun x => probabilityCurrentValue1D ℏ κ (ψ x) (ψx x)) := by
  have hcurrent : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => probabilityCurrentValue1D ℏ κ (ψ y) (ψx y))
        (probabilityCurrentDivergenceValue1D ℏ κ (ψ x) (ψxx x)) x := by
    intro x hx
    exact hasDerivAt_probabilityCurrentValue1D ℏ κ
      (hψ x hx) (hψx x hx)
  have hweak := ConservationLaw.weak_continuity_interval_of_pointwise
    (ContinuousLinearMap.mul ℝ ℝ) (a := a) (b := b)
    (test := test) (testDerivative := testDerivative)
    (current := fun x => probabilityCurrentValue1D ℏ κ (ψ x) (ψx x))
    (currentDerivative := fun x =>
      probabilityCurrentDivergenceValue1D ℏ κ (ψ x) (ψxx x))
    (densityTimeDerivative := fun x =>
      probabilityDensityTimeDerivativeValue (ψ x) (ψt x))
    (by intro x
        exact probability_continuity_balance_of_schrodinger
          ℏ κ (potential x) (ψ x) (ψt x) (ψxx x) hℏ (hschrodinger x))
    htest hcurrent
    (htestIntegrable.mul_continuousOn (HasDerivAt.continuousOn hcurrent))
    (hcurrentIntegrable.continuousOn_mul (HasDerivAt.continuousOn htest))
  simpa only [weightedBoundaryCurrent1D, ContinuousLinearMap.mul_apply'] using hweak

end
end Continuum
end SingleParticle
end QuantumMechanics
