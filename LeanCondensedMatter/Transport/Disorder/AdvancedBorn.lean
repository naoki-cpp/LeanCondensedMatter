import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.BornCommon
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Advanced finite-disorder Born self-energy and closure boundary

This module provides conventional advanced physical names for the side-indexed Born data owned by
`Disorder.BornCommon`, and specializes the centered exact-average decomposition proved there from
the exact side-indexed configuration Dyson identities.

The exact second-order remainder, closure error, and closure hypothesis are canonical side-indexed
objects in `BornCommon`; the declarations here are advanced specializations. Their retarded and
advanced canonical forms are related by adjunction upstream, so no independent covariance or
closure-error relation is supplied here.

No self-consistency, vertex resummation, Ward identity, trace-per-volume construction, or
thermodynamic limit is introduced.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Advanced specialization of the canonical exact second-order Dyson remainder. -/
noncomputable def exactSecondOrderAdvancedRemainder
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondOrderRemainder .advanced energy broadening

/-- For centered disorder, the exact averaged advanced Green operator is the clean advanced Green
operator plus the full exact second-order remainder. -/
theorem averagedAdvancedGreen_eq_free_add_exactRemainder
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.averagedAdvancedGreen energy broadening =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.exactSecondOrderAdvancedRemainder energy broadening := by
  simpa [averagedAdvancedGreen, exactSecondOrderAdvancedRemainder] using
    averagedGreen_eq_free_add_exactSecondOrderRemainder
      ensemble hcentered .advanced energy broadening hbroadening

/-- Conventional advanced name for the canonical side-indexed first-Born self-energy. -/
noncomputable def bornAdvancedSelfEnergy
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornSelfEnergy .advanced energy broadening

/-- The advanced Born self-energy is the exact finite second moment with a clean advanced internal
propagator. -/
theorem bornAdvancedSelfEnergy_eq_secondMoment
    (energy broadening : ℝ) :
    bornAdvancedSelfEnergy ensemble energy broadening =
      ensemble.exactSecondMoment (ensemble.freeAdvancedGreen energy broadening) := by
  rw [bornAdvancedSelfEnergy, bornSelfEnergy_eq_secondMoment, freeGreen_advanced]

@[simp]
theorem bornSelfEnergy_advanced
    (energy broadening : ℝ) :
    ensemble.bornSelfEnergy .advanced energy broadening =
      ensemble.bornAdvancedSelfEnergy energy broadening :=
  rfl

/-- Conventional advanced name for the canonical side-indexed second-order Born approximation.
This definition does not require centering. -/
noncomputable def bornAdvancedResolventApproximation
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornResolventApproximation .advanced energy broadening

@[simp]
theorem bornResolventApproximation_advanced
    (energy broadening : ℝ) :
    ensemble.bornResolventApproximation .advanced energy broadening =
      ensemble.bornAdvancedResolventApproximation energy broadening :=
  rfl

/-- Advanced specialization of the canonical exact Born closure error. -/
noncomputable def bornAdvancedClosureError
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornClosureError .advanced energy broadening

/-- Exact decomposition of the averaged advanced Green operator into the Born approximation plus
its retained closure error. Centering is used only through the exact averaged-Dyson reduction. -/
theorem averagedAdvancedGreen_eq_bornApproximation_add_error
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.averagedAdvancedGreen energy broadening =
      bornAdvancedResolventApproximation ensemble energy broadening +
        bornAdvancedClosureError ensemble energy broadening := by
  rw [averagedAdvancedGreen_eq_free_add_exactRemainder
    ensemble hcentered energy broadening hbroadening]
  unfold bornAdvancedResolventApproximation bornAdvancedClosureError bornClosureError
  rw [ensemble.freeGreen_advanced, ensemble.bornSelfEnergy_advanced]
  exact free_add_remainder_eq_bornApproximation_add_error
    (ensemble.freeAdvancedGreen energy broadening)
    (ensemble.exactSecondOrderAdvancedRemainder energy broadening)
    (bornAdvancedSelfEnergy ensemble energy broadening)

/-- Advanced physical specialization of the canonical side-indexed Born closure hypothesis. -/
abbrev AdvancedBornClosureHypothesis
    (energy broadening : ℝ) : Prop :=
  ensemble.BornClosureHypothesis .advanced energy broadening

/-- Equality with the advanced Born approximation follows only under both centered disorder and the
explicit closure hypothesis. -/
theorem averagedAdvancedGreen_eq_bornApproximation
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening)
    (closure : AdvancedBornClosureHypothesis ensemble energy broadening) :
    ensemble.averagedAdvancedGreen energy broadening =
      bornAdvancedResolventApproximation ensemble energy broadening := by
  rw [averagedAdvancedGreen_eq_bornApproximation_add_error
    ensemble hcentered energy broadening hbroadening]
  have hclosure : bornAdvancedClosureError ensemble energy broadening = 0 := by
    simpa [bornAdvancedClosureError] using closure.closureError_eq_zero
  rw [hclosure, add_zero]

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
