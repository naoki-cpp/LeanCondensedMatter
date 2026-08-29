import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.BornCommon
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Retarded finite-disorder Born self-energy and closure boundary

This module provides conventional retarded physical names for the side-indexed Born data owned by
`Disorder.BornCommon`, and proves the centered exact-average decomposition using the exact retarded
configuration Dyson identity from `Disorder.Resolvent`.

The exact second-order remainder, closure error, and closure hypothesis are canonical side-indexed
objects in `BornCommon`; the declarations here are retarded specializations. The exact averaged
Green operator is not identified with the Born expression by definition: equality requires the
explicit retarded specialization of `BornClosureHypothesis`.

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

private theorem operatorAverage_firstOrderRetardedTerm_eq_zero
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) :
    ensemble.operatorAverage (fun ω =>
      ensemble.freeRetardedGreen energy broadening *
        (ensemble.impurityPotential ω).1 *
          ensemble.freeRetardedGreen energy broadening) = 0 := by
  simpa using operatorAverage_mul_impurity_mul_eq_zero ensemble hcentered
    (ensemble.freeRetardedGreen energy broadening)
    (ensemble.freeRetardedGreen energy broadening)

/-- Retarded specialization of the canonical exact second-order Dyson remainder. -/
noncomputable def exactSecondOrderRetardedRemainder
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondOrderRemainder .retarded energy broadening

/-- For centered disorder, the exact averaged retarded Green operator is the clean resolvent plus
the full exact second-order remainder. No Born closure has been made. -/
theorem averagedRetardedGreen_eq_free_add_exactRemainder
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.averagedRetardedGreen energy broadening =
      ensemble.freeRetardedGreen energy broadening +
        ensemble.exactSecondOrderRetardedRemainder energy broadening := by
  simpa [averagedRetardedGreen, averagedGreen, exactSecondOrderRetardedRemainder] using
    operatorAverage_eq_free_add_remainder_of_secondOrder
      ensemble
      (ensemble.freeRetardedGreen energy broadening)
      (fun ω => ensemble.configurationRetardedGreen energy broadening ω)
      (fun ω =>
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening)
      (fun ω =>
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationRetardedGreen energy broadening ω)
      (configurationRetardedGreen_eq_secondOrder_add_exactRemainder
        ensemble energy broadening hbroadening)
      (operatorAverage_firstOrderRetardedTerm_eq_zero
        ensemble hcentered energy broadening)

/-- Conventional retarded name for the canonical side-indexed first-Born self-energy. -/
noncomputable def bornRetardedSelfEnergy
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornSelfEnergy .retarded energy broadening

/-- The Born self-energy is the exact finite second moment with a clean retarded internal
propagator. -/
theorem bornRetardedSelfEnergy_eq_secondMoment
    (energy broadening : ℝ) :
    bornRetardedSelfEnergy ensemble energy broadening =
      ensemble.exactSecondMoment (ensemble.freeRetardedGreen energy broadening) := by
  rw [bornRetardedSelfEnergy, bornSelfEnergy_eq_secondMoment, freeGreen_retarded]

@[simp]
theorem bornSelfEnergy_retarded
    (energy broadening : ℝ) :
    ensemble.bornSelfEnergy .retarded energy broadening =
      ensemble.bornRetardedSelfEnergy energy broadening :=
  rfl

/-- Conventional retarded name for the canonical side-indexed second-order Born approximation.
It is deliberately not an equality theorem for the exact average and does not require centering. -/
noncomputable def bornRetardedResolventApproximation
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornResolventApproximation .retarded energy broadening

@[simp]
theorem bornResolventApproximation_retarded
    (energy broadening : ℝ) :
    ensemble.bornResolventApproximation .retarded energy broadening =
      ensemble.bornRetardedResolventApproximation energy broadening :=
  rfl

/-- Retarded specialization of the canonical exact Born closure error. -/
noncomputable def bornRetardedClosureError
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.bornClosureError .retarded energy broadening

/-- Exact decomposition of the averaged retarded Green operator into the named Born approximation
plus its closure error. Centering is used only through the exact averaged-Dyson reduction. -/
theorem averagedRetardedGreen_eq_bornApproximation_add_error
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.averagedRetardedGreen energy broadening =
      bornRetardedResolventApproximation ensemble energy broadening +
        bornRetardedClosureError ensemble energy broadening := by
  rw [averagedRetardedGreen_eq_free_add_exactRemainder
    ensemble hcentered energy broadening hbroadening]
  unfold bornRetardedResolventApproximation bornRetardedClosureError bornClosureError
  rw [ensemble.freeGreen_retarded, ensemble.bornSelfEnergy_retarded]
  exact free_add_remainder_eq_bornApproximation_add_error
    (ensemble.freeRetardedGreen energy broadening)
    (ensemble.exactSecondOrderRetardedRemainder energy broadening)
    (bornRetardedSelfEnergy ensemble energy broadening)

/-- Retarded physical specialization of the canonical side-indexed Born closure hypothesis. -/
abbrev RetardedBornClosureHypothesis
    (energy broadening : ℝ) : Prop :=
  ensemble.BornClosureHypothesis .retarded energy broadening

/-- Equality with the Born approximation follows only after supplying both centered disorder and
the explicit closure hypothesis. -/
theorem averagedRetardedGreen_eq_bornApproximation
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening)
    (closure : RetardedBornClosureHypothesis ensemble energy broadening) :
    ensemble.averagedRetardedGreen energy broadening =
      bornRetardedResolventApproximation ensemble energy broadening := by
  rw [averagedRetardedGreen_eq_bornApproximation_add_error
    ensemble hcentered energy broadening hbroadening]
  have hclosure : bornRetardedClosureError ensemble energy broadening = 0 := by
    simpa [bornRetardedClosureError] using closure.closureError_eq_zero
  rw [hclosure, add_zero]

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
