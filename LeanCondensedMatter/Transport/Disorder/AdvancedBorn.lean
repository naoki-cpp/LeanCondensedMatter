import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.BornCommon
import LeanCondensedMatter.Transport.Disorder.Resolvent

set_option linter.style.header false

/-!
# Advanced finite-disorder Born self-energy and closure boundary

Exact retarded/advanced Green operators and configuration-wise Dyson identities are owned by
`Disorder.Resolvent`. This module consumes those exact identities together with the canonical exact
second moment and explicit centering property from `Disorder.Moments` and the R/A-neutral proof
algebra from `Disorder.BornCommon`.

The advanced specialization uses the same exact finite second-moment action as the retarded
specialization, but keeps its orientation-sensitive Dyson remainder and physical names locally.
The Born objects themselves do not require centered disorder; centering enters when the exact
averaged Dyson expansion is reduced by cancellation of the first-order term. No self-consistency,
vertex resummation, Ward identity, trace-per-volume construction, or thermodynamic limit is
introduced.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

private theorem operatorAverage_firstOrderAdvancedTerm_eq_zero
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) :
    ensemble.operatorAverage (fun ω =>
      ensemble.freeAdvancedGreen energy broadening *
        (ensemble.impurityPotential ω).1 *
          ensemble.freeAdvancedGreen energy broadening) = 0 := by
  simpa using operatorAverage_mul_impurity_mul_eq_zero ensemble hcentered
    (ensemble.freeAdvancedGreen energy broadening)
    (ensemble.freeAdvancedGreen energy broadening)

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
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationAdvancedGreen energy broadening ω) =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.exactSecondOrderAdvancedRemainder energy broadening := by
  simpa [exactSecondOrderAdvancedRemainder] using
    operatorAverage_eq_free_add_remainder_of_secondOrder
      ensemble
      (ensemble.freeAdvancedGreen energy broadening)
      (fun ω => ensemble.configurationAdvancedGreen energy broadening ω)
      (fun ω =>
        ensemble.freeAdvancedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening)
      (fun ω =>
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening)
      (configurationAdvancedGreen_eq_secondOrder_add_exactRemainder
        ensemble energy broadening hbroadening)
      (operatorAverage_firstOrderAdvancedTerm_eq_zero
        ensemble hcentered energy broadening)

/-- Weak-scattering advanced Born self-energy: the exact finite second moment evaluated on the
clean advanced Green operator. The definition itself does not require centered disorder. -/
noncomputable def bornAdvancedSelfEnergy
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondMoment (ensemble.freeAdvancedGreen energy broadening)

/-- The advanced Born self-energy is the exact finite second moment with a clean advanced internal
propagator. -/
theorem bornAdvancedSelfEnergy_eq_secondMoment
    (energy broadening : ℝ) :
    bornAdvancedSelfEnergy ensemble energy broadening =
      ensemble.exactSecondMoment (ensemble.freeAdvancedGreen energy broadening) :=
  rfl

/-- Canonical second-order Born approximation to the averaged advanced Green operator. This
definition does not require centering. -/
noncomputable def bornAdvancedResolventApproximation
    (energy broadening : ℝ) : H →L[ℂ] H :=
  secondOrderBornResolventApproximation
    (ensemble.freeAdvancedGreen energy broadening)
    (bornAdvancedSelfEnergy ensemble energy broadening)

/-- Exact error between the full averaged advanced Dyson remainder and the advanced Born closure.
Its definition does not assert that centered disorder holds or that the error is small. -/
noncomputable def bornAdvancedClosureError
    (energy broadening : ℝ) : H →L[ℂ] H :=
  secondOrderBornClosureError
    (ensemble.freeAdvancedGreen energy broadening)
    (ensemble.exactSecondOrderAdvancedRemainder energy broadening)
    (bornAdvancedSelfEnergy ensemble energy broadening)

/-- Exact decomposition of the averaged advanced Green operator into the Born approximation plus
its retained closure error. Centering is used only through the exact averaged-Dyson reduction. -/
theorem operatorAverage_configurationAdvancedGreen_eq_bornApproximation_add_error
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationAdvancedGreen energy broadening ω) =
      bornAdvancedResolventApproximation ensemble energy broadening +
        bornAdvancedClosureError ensemble energy broadening := by
  rw [operatorAverage_configurationAdvancedGreen_eq_free_add_exactRemainder
    ensemble hcentered energy broadening hbroadening]
  unfold bornAdvancedResolventApproximation bornAdvancedClosureError
  exact free_add_remainder_eq_bornApproximation_add_error
    (ensemble.freeAdvancedGreen energy broadening)
    (ensemble.exactSecondOrderAdvancedRemainder energy broadening)
    (bornAdvancedSelfEnergy ensemble energy broadening)

/-- Explicit closure hypothesis required before identifying the exact advanced average with its
second-order Born approximation. Centering is a separate hypothesis on the exact averaging theorem. -/
structure AdvancedBornClosureHypothesis
    (energy broadening : ℝ) : Prop where
  /-- The retained exact advanced closure error vanishes. -/
  closureError_eq_zero :
    bornAdvancedClosureError ensemble energy broadening = 0

/-- Equality with the advanced Born approximation follows only under both centered disorder and the
explicit closure hypothesis. -/
theorem operatorAverage_configurationAdvancedGreen_eq_bornApproximation
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening)
    (closure : AdvancedBornClosureHypothesis ensemble energy broadening) :
    ensemble.operatorAverage
        (fun ω => ensemble.configurationAdvancedGreen energy broadening ω) =
      bornAdvancedResolventApproximation ensemble energy broadening := by
  rw [operatorAverage_configurationAdvancedGreen_eq_bornApproximation_add_error
    ensemble hcentered energy broadening hbroadening]
  rw [AdvancedBornClosureHypothesis.closureError_eq_zero closure, add_zero]

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
