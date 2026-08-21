import LeanCondensedMatter.Transport.FiniteDisorder
import LeanCondensedMatter.Transport.Resolvent

set_option linter.style.header false

/-!
# Finite-disorder Born self-energy and exact Dyson remainder

This module separates three logically distinct objects:

1. exact finite disorder moments;
2. an exact second-order resolvent/Dyson expansion with its full remainder; and
3. the weak-scattering Born closure obtained by dropping that remainder error.

A `FiniteDisorderMomentData` bundles explicit centering and covariance assumptions. The Born
self-energy is the covariance action on the clean retarded resolvent. The exact averaged resolvent
is not identified with the Born expression by definition: their difference is named
`bornRetardedClosureError`, and equality requires an explicit `RetardedBornClosureHypothesis`.

Exact scalar/operator averaging is owned by `FiniteDisorder`; this module only consumes that layer
to state the moment, Dyson, and Born boundaries.

No self-consistent Born approximation, dressed propagator inside the self-energy, vertex
correction, Ward identity, trace-per-volume construction, or thermodynamic limit is introduced.
-/

namespace QuantumTheory
namespace Transport

open scoped BigOperators

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Exact clean retarded Green operator used in the Born expansion. -/
noncomputable def freeRetardedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  retardedResolvent ensemble.baseHamiltonian.1 energy broadening

/-- Exact retarded Green operator of one disordered configuration. -/
noncomputable def configurationRetardedGreen
    (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening

/-- Exact first resolvent identity
`Gω = G₀ + G₀ Vω Gω` at positive retarded broadening. -/
theorem configurationRetardedGreen_eq_free_add_dyson
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedGreen energy broadening ω =
      ensemble.freeRetardedGreen energy broadening +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationRetardedGreen energy broadening ω := by
  unfold configurationRetardedGreen freeRetardedGreen
  let shift₀ : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy broadening) -
      ensemble.baseHamiltonian.1
  let shiftω : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy broadening) -
      (ensemble.configurationHamiltonian ω).1
  have hshift : shift₀ = shiftω + (ensemble.impurityPotential ω).1 := by
    dsimp [shift₀, shiftω, FiniteDisorderEnsemble.configurationHamiltonian]
    noncomm_ring
  have hfree := resolvent_mul_retardedShift
    ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
    energy broadening hbroadening
  have hconfiguration := retardedShift_mul_resolvent
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2
    energy broadening hbroadening
  change retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening = _
  calc
    retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening =
        retardedResolvent ensemble.baseHamiltonian.1 energy broadening * shift₀ *
          retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      rw [hfree]
      simp
    _ = retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (shiftω + (ensemble.impurityPotential ω).1) *
            retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      rw [hshift]
    _ = retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (shiftω * retardedResolvent
            (ensemble.configurationHamiltonian ω).1 energy broadening) +
        retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (ensemble.impurityPotential ω).1 *
            retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      noncomm_ring
    _ = retardedResolvent ensemble.baseHamiltonian.1 energy broadening +
        retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (ensemble.impurityPotential ω).1 *
            retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      rw [hconfiguration]
      simp

/-- Exact second-order Dyson expansion with the full configuration resolvent retained in the
remainder. This is an identity, not a weak-scattering approximation. -/
theorem configurationRetardedGreen_eq_secondOrder_add_exactRemainder
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedGreen energy broadening ω =
      ensemble.freeRetardedGreen energy broadening +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationRetardedGreen energy broadening ω := by
  have hdyson := configurationRetardedGreen_eq_free_add_dyson
    ensemble energy broadening hbroadening ω
  calc
    ensemble.configurationRetardedGreen energy broadening ω =
        ensemble.freeRetardedGreen energy broadening +
          ensemble.freeRetardedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              ensemble.configurationRetardedGreen energy broadening ω := hdyson
    _ = ensemble.freeRetardedGreen energy broadening +
          ensemble.freeRetardedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              (ensemble.freeRetardedGreen energy broadening +
                ensemble.freeRetardedGreen energy broadening *
                  (ensemble.impurityPotential ω).1 *
                    ensemble.configurationRetardedGreen energy broadening ω) := by
      exact congrArg
        (fun green : H →L[ℂ] H =>
          ensemble.freeRetardedGreen energy broadening +
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 * green)
        hdyson
    _ = _ := by
      noncomm_ring

/-- Explicit centered-disorder and covariance assumptions for a finite ensemble. The covariance is
an operator-valued action on a supplied kernel; its exact finite second-moment realization is stored
as a field. -/
structure FiniteDisorderMomentData where
  /-- Operator-valued covariance action on an inserted bounded kernel. -/
  covariance : (H →L[ℂ] H) → H →L[ℂ] H
  /-- Exact centering condition `E[Vω] = 0`. -/
  centered :
    ensemble.operatorAverage (fun ω => (ensemble.impurityPotential ω).1) = 0
  /-- Identification of the covariance action with the exact weighted finite second moment. -/
  covariance_eq_secondMoment : ∀ kernel,
    covariance kernel =
      ensemble.operatorAverage (fun ω =>
        (ensemble.impurityPotential ω).1 * kernel *
          (ensemble.impurityPotential ω).1)

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
