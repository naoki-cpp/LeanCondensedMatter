import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Finite-disorder Born self-energy and closure boundary

This module starts from the exact finite ensemble and exact configuration-wise resolvent/Dyson
identities owned by `Disorder.Finite` and `Disorder.Resolvent`, together with centered finite
second-moment data owned by `Disorder.Moments`.

From those moments, the module forms the exact averaged second-order Dyson remainder and then defines
the weak-scattering Born self-energy and resolvent approximation. The exact averaged resolvent is not
identified with the Born expression by definition: their difference is named
`bornRetardedClosureError`, and equality requires an explicit `RetardedBornClosureHypothesis`.

No advanced Born closure, self-consistent Born approximation, dressed propagator inside the
self-energy, vertex correction, Ward identity, trace-per-volume construction, or thermodynamic
limit is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- The first-order averaged Dyson term vanishes exactly for centered disorder. -/
theorem operatorAverage_firstOrderRetardedTerm_eq_zero
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) :
    ensemble.operatorAverage (fun ω =>
      ensemble.freeRetardedGreen energy broadening *
        (ensemble.impurityPotential ω).1 *
          ensemble.freeRetardedGreen energy broadening) = 0 := by
  rw [operatorAverage_mul_left_right ensemble]
  rw [FiniteDisorderMomentData.centered moments]
  simp

/-- Exact finite average of the full second-order Dyson remainder. -/
noncomputable def exactSecondOrderRetardedRemainder
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    ensemble.freeRetardedGreen energy broadening *
      (ensemble.impurityPotential ω).1 *
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationRetardedGreen energy broadening ω)

/-- For centered disorder, the averaged exact resolvent is the clean resolvent plus the full exact
second-order remainder. No Born closure has been made. -/
theorem operatorAverage_configurationRetardedGreen_eq_free_add_exactRemainder
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationRetardedGreen energy broadening ω) =
      ensemble.freeRetardedGreen energy broadening +
        ensemble.exactSecondOrderRetardedRemainder energy broadening := by
  calc
    ensemble.operatorAverage
        (fun ω => ensemble.configurationRetardedGreen energy broadening ω) =
      ensemble.operatorAverage (fun ω =>
        (ensemble.freeRetardedGreen energy broadening +
          ensemble.freeRetardedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeRetardedGreen energy broadening) +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationRetardedGreen energy broadening ω) := by
      apply congrArg ensemble.operatorAverage
      funext ω
      exact configurationRetardedGreen_eq_secondOrder_add_exactRemainder
        ensemble energy broadening hbroadening ω
    _ = ensemble.operatorAverage (fun ω =>
          ensemble.freeRetardedGreen energy broadening +
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeRetardedGreen energy broadening) +
        ensemble.exactSecondOrderRetardedRemainder energy broadening := by
      rw [operatorAverage_add ensemble]
      rfl
    _ = (ensemble.operatorAverage
          (fun _ => ensemble.freeRetardedGreen energy broadening) +
        ensemble.operatorAverage (fun ω =>
          ensemble.freeRetardedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeRetardedGreen energy broadening)) +
        ensemble.exactSecondOrderRetardedRemainder energy broadening := by
      rw [operatorAverage_add ensemble]
    _ = ensemble.freeRetardedGreen energy broadening +
        ensemble.exactSecondOrderRetardedRemainder energy broadening := by
      rw [operatorAverage_const ensemble]
      rw [operatorAverage_firstOrderRetardedTerm_eq_zero ensemble moments]
      simp

/-- Weak-scattering Born self-energy: covariance acting on the clean retarded Green operator. The
name records its approximation status; no dressed self-consistent propagator is inserted. -/
noncomputable def bornRetardedSelfEnergy
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  moments.covariance (ensemble.freeRetardedGreen energy broadening)

/-- The Born self-energy is the exact finite second moment with a clean internal propagator. -/
theorem bornRetardedSelfEnergy_eq_secondMoment
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) :
    bornRetardedSelfEnergy ensemble moments energy broadening =
      ensemble.operatorAverage (fun ω =>
        (ensemble.impurityPotential ω).1 *
          ensemble.freeRetardedGreen energy broadening *
            (ensemble.impurityPotential ω).1) :=
  FiniteDisorderMomentData.covariance_eq_secondMoment moments
    (ensemble.freeRetardedGreen energy broadening)

/-- Canonical second-order Born approximation to the averaged retarded resolvent. This definition
is deliberately not an equality theorem for the exact average. -/
noncomputable def bornRetardedResolventApproximation
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.freeRetardedGreen energy broadening +
    ensemble.freeRetardedGreen energy broadening *
      bornRetardedSelfEnergy ensemble moments energy broadening *
        ensemble.freeRetardedGreen energy broadening

/-- Exact error between the full averaged Dyson remainder and the Born second-order closure. -/
noncomputable def bornRetardedClosureError
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondOrderRetardedRemainder energy broadening -
    ensemble.freeRetardedGreen energy broadening *
      bornRetardedSelfEnergy ensemble moments energy broadening *
        ensemble.freeRetardedGreen energy broadening

/-- Exact decomposition of the averaged resolvent into the named Born approximation plus its
closure error. This theorem does not assert that the error is small or zero. -/
theorem operatorAverage_configurationRetardedGreen_eq_bornApproximation_add_error
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationRetardedGreen energy broadening ω) =
      bornRetardedResolventApproximation ensemble moments energy broadening +
        bornRetardedClosureError ensemble moments energy broadening := by
  rw [operatorAverage_configurationRetardedGreen_eq_free_add_exactRemainder
    ensemble moments energy broadening hbroadening]
  unfold bornRetardedResolventApproximation bornRetardedClosureError
  noncomm_ring

/-- Explicit closure hypothesis required to turn the second-order Born approximation into an exact
equality statement. In weak-scattering applications this field represents the neglected higher
order remainder; it is not derived in this module. -/
structure RetardedBornClosureHypothesis
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) : Prop where
  closureError_eq_zero :
    bornRetardedClosureError ensemble moments energy broadening = 0

/-- Equality with the Born approximation follows only after supplying the explicit closure
hypothesis. -/
theorem operatorAverage_configurationRetardedGreen_eq_bornApproximation
    (moments : FiniteDisorderMomentData ensemble)
    (energy broadening : ℝ) (hbroadening : 0 < broadening)
    (closure : RetardedBornClosureHypothesis ensemble moments energy broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationRetardedGreen energy broadening ω) =
      bornRetardedResolventApproximation ensemble moments energy broadening := by
  rw [operatorAverage_configurationRetardedGreen_eq_bornApproximation_add_error
    ensemble moments energy broadening hbroadening]
  rw [RetardedBornClosureHypothesis.closureError_eq_zero closure, add_zero]

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
