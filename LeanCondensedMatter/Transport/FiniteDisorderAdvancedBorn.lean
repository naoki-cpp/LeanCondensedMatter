import LeanCondensedMatter.Transport.FiniteDisorderBorn

set_option linter.style.header false

/-!
# Advanced finite-disorder Born self-energy

This module mirrors the retarded weak-scattering boundary with advanced Green operators. It proves
an exact right-oriented Dyson identity, iterates it once with the complete configuration Green
operator retained in the remainder, and separates the advanced Born approximation from its exact
closure error.

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

/-- Exact clean advanced Green operator used in the Born expansion. -/
noncomputable def freeAdvancedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  advancedResolvent ensemble.baseHamiltonian.1 energy broadening

/-- Exact advanced Green operator of one disordered configuration. -/
noncomputable def configurationAdvancedGreen
    (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening

/-- The clean advanced Green operator is the adjoint of the clean retarded Green operator. -/
theorem star_freeRetardedGreen
    (energy broadening : ℝ) :
    star (ensemble.freeRetardedGreen energy broadening) =
      ensemble.freeAdvancedGreen energy broadening := by
  unfold freeRetardedGreen freeAdvancedGreen
  exact star_retardedResolvent
    ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy broadening

/-- The configuration advanced Green operator is the adjoint of the corresponding retarded Green
operator. -/
theorem star_configurationRetardedGreen
    (energy broadening : ℝ) (ω : Ω) :
    star (ensemble.configurationRetardedGreen energy broadening ω) =
      ensemble.configurationAdvancedGreen energy broadening ω := by
  unfold configurationRetardedGreen configurationAdvancedGreen
  exact star_retardedResolvent
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2 energy broadening

/-- Exact right-oriented advanced resolvent identity
`Gωᴬ = G₀ᴬ + Gωᴬ Vω G₀ᴬ` at positive broadening. -/
theorem configurationAdvancedGreen_eq_free_add_dyson
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationAdvancedGreen energy broadening ω =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening := by
  unfold configurationAdvancedGreen freeAdvancedGreen
  let shift₀ : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (advancedSpectralParameter energy broadening) -
      ensemble.baseHamiltonian.1
  let shiftω : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (advancedSpectralParameter energy broadening) -
      (ensemble.configurationHamiltonian ω).1
  have hshift : shift₀ = shiftω + (ensemble.impurityPotential ω).1 := by
    dsimp [shift₀, shiftω, FiniteDisorderEnsemble.configurationHamiltonian]
    noncomm_ring
  have hfree := advancedShift_mul_resolvent
    ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energy broadening hbroadening
  have hconfiguration := resolvent_mul_advancedShift
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2
      energy broadening hbroadening
  change advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening = _
  calc
    advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening =
        advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening *
          shift₀ * advancedResolvent ensemble.baseHamiltonian.1 energy broadening := by
      rw [← mul_assoc, hfree, mul_one]
    _ = advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening *
          (shiftω + (ensemble.impurityPotential ω).1) *
            advancedResolvent ensemble.baseHamiltonian.1 energy broadening := by
      rw [hshift]
    _ = (advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening *
            shiftω) * advancedResolvent ensemble.baseHamiltonian.1 energy broadening +
        advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening *
          (ensemble.impurityPotential ω).1 *
            advancedResolvent ensemble.baseHamiltonian.1 energy broadening := by
      noncomm_ring
    _ = advancedResolvent ensemble.baseHamiltonian.1 energy broadening +
        advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening *
          (ensemble.impurityPotential ω).1 *
            advancedResolvent ensemble.baseHamiltonian.1 energy broadening := by
      rw [hconfiguration, one_mul]

/-- Exact second-order advanced Dyson expansion with the full configuration Green operator retained
in the remainder. This remains an identity rather than a Born closure. -/
theorem configurationAdvancedGreen_eq_secondOrder_add_exactRemainder
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationAdvancedGreen energy broadening ω =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.freeAdvancedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening +
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening := by
  have hdyson := configurationAdvancedGreen_eq_free_add_dyson
    ensemble energy broadening hbroadening ω
  calc
    ensemble.configurationAdvancedGreen energy broadening ω =
        ensemble.freeAdvancedGreen energy broadening +
          ensemble.configurationAdvancedGreen energy broadening ω *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeAdvancedGreen energy broadening := hdyson
    _ = ensemble.freeAdvancedGreen energy broadening +
          (ensemble.freeAdvancedGreen energy broadening +
            ensemble.configurationAdvancedGreen energy broadening ω *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening) *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeAdvancedGreen energy broadening := by
      exact congrArg
        (fun green : H →L[ℂ] H =>
          ensemble.freeAdvancedGreen energy broadening +
            green * (ensemble.impurityPotential ω).1 *
              ensemble.freeAdvancedGreen energy broadening)
        hdyson
    _ = _ := by
      noncomm_ring

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
