import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Advanced finite-disorder Born self-energy and closure boundary

Exact retarded/advanced Green operators and configuration-wise Dyson identities are owned by
`Disorder.Resolvent`. This module consumes those exact identities together with the centered
finite-disorder moment data from `Disorder.Moments` and defines the advanced averaged remainder,
Born self-energy, resolvent approximation, and explicit closure error.

The advanced Born self-energy uses the same centered finite-disorder covariance action as the
retarded self-energy. No self-consistency, vertex resummation, Ward identity, trace-per-volume
construction, or thermodynamic limit is introduced.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- The first-order advanced Dyson contribution vanishes exactly for centered disorder. -/
theorem operatorAverage_firstOrderAdvancedTerm_eq_zero
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) :
    ensemble.operatorAverage (fun ω =>
      ensemble.freeAdvancedGreen energy broadening *
        (ensemble.impurityPotential ω).1 *
          ensemble.freeAdvancedGreen energy broadening) = 0 := by
  rw [operatorAverage_mul_left_right ensemble]
  rw [FiniteDisorderMomentData.centered moments]
  simp

/-- Exact finite average of the full advanced second-order Dyson remainder. -/
noncomputable def exactSecondOrderAdvancedRemainder
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    ensemble.configurationAdvancedGreen energy broadening ω *
      (ensemble.impurityPotential ω).1 *
        ensemble.freeAdvancedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening)

/-- For centered disorder, the exact averaged advanced Green operator is the clean advanced Green
operator plus the full exact second-order remainder. -/
theorem operatorAverage_configurationAdvancedGreen_eq_free_add_exactRemainder
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationAdvancedGreen energy broadening ω) =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.exactSecondOrderAdvancedRemainder energy broadening := by
  calc
    ensemble.operatorAverage
        (fun ω => ensemble.configurationAdvancedGreen energy broadening ω) =
      ensemble.operatorAverage (fun ω =>
        (ensemble.freeAdvancedGreen energy broadening +
          ensemble.freeAdvancedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeAdvancedGreen energy broadening) +
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening) := by
      apply congrArg ensemble.operatorAverage
      funext ω
      exact configurationAdvancedGreen_eq_secondOrder_add_exactRemainder
        ensemble energy broadening hbroadening ω
    _ = ensemble.operatorAverage (fun ω =>
          ensemble.freeAdvancedGreen energy broadening +
            ensemble.freeAdvancedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening) +
        ensemble.exactSecondOrderAdvancedRemainder energy broadening := by
      rw [operatorAverage_add ensemble]
      rfl
    _ = (ensemble.operatorAverage
          (fun _ => ensemble.freeAdvancedGreen energy broadening) +
        ensemble.operatorAverage (fun ω =>
          ensemble.freeAdvancedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeAdvancedGreen energy broadening)) +
        ensemble.exactSecondOrderAdvancedRemainder energy broadening := by
      rw [operatorAverage_add ensemble]
    _ = ensemble.freeAdvancedGreen energy broadening +
        ensemble.exactSecondOrderAdvancedRemainder energy broadening := by
      rw [operatorAverage_const ensemble]
      rw [operatorAverage_firstOrderAdvancedTerm_eq_zero ensemble moments]
      simp

/-- Weak-scattering advanced Born self-energy: the same covariance action evaluated on the clean
advanced Green operator. -/
noncomputable def bornAdvancedSelfEnergy
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  moments.covariance (ensemble.freeAdvancedGreen energy broadening)

/-- The advanced Born self-energy is the exact finite second moment with a clean advanced internal
propagator. -/
theorem bornAdvancedSelfEnergy_eq_secondMoment
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) :
    bornAdvancedSelfEnergy ensemble moments energy broadening =
      ensemble.operatorAverage (fun ω =>
        (ensemble.impurityPotential ω).1 *
          ensemble.freeAdvancedGreen energy broadening *
            (ensemble.impurityPotential ω).1) :=
  FiniteDisorderMomentData.covariance_eq_secondMoment moments
    (ensemble.freeAdvancedGreen energy broadening)

/-- Canonical second-order Born approximation to the averaged advanced Green operator. -/
noncomputable def bornAdvancedResolventApproximation
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.freeAdvancedGreen energy broadening +
    ensemble.freeAdvancedGreen energy broadening *
      bornAdvancedSelfEnergy ensemble moments energy broadening *
        ensemble.freeAdvancedGreen energy broadening

/-- Exact error between the full averaged advanced Dyson remainder and the advanced Born closure. -/
noncomputable def bornAdvancedClosureError
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondOrderAdvancedRemainder energy broadening -
    ensemble.freeAdvancedGreen energy broadening *
      bornAdvancedSelfEnergy ensemble moments energy broadening *
        ensemble.freeAdvancedGreen energy broadening

/-- Exact decomposition of the averaged advanced Green operator into the Born approximation plus
its retained closure error. -/
theorem operatorAverage_configurationAdvancedGreen_eq_bornApproximation_add_error
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationAdvancedGreen energy broadening ω) =
      bornAdvancedResolventApproximation ensemble moments energy broadening +
        bornAdvancedClosureError ensemble moments energy broadening := by
  rw [operatorAverage_configurationAdvancedGreen_eq_free_add_exactRemainder
    ensemble moments energy broadening hbroadening]
  unfold bornAdvancedResolventApproximation bornAdvancedClosureError
  noncomm_ring

/-- Explicit closure hypothesis required before identifying the exact advanced average with its
second-order Born approximation. -/
structure AdvancedBornClosureHypothesis
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : Prop where
  /-- The retained exact advanced closure error vanishes. -/
  closureError_eq_zero :
    bornAdvancedClosureError ensemble moments energy broadening = 0

/-- Equality with the advanced Born approximation follows only under the explicit closure
hypothesis. -/
theorem operatorAverage_configurationAdvancedGreen_eq_bornApproximation
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) (hbroadening : 0 < broadening)
    (closure : AdvancedBornClosureHypothesis ensemble moments energy broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationAdvancedGreen energy broadening ω) =
      bornAdvancedResolventApproximation ensemble moments energy broadening := by
  rw [operatorAverage_configurationAdvancedGreen_eq_bornApproximation_add_error
    ensemble moments energy broadening hbroadening]
  rw [AdvancedBornClosureHypothesis.closureError_eq_zero closure, add_zero]

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
