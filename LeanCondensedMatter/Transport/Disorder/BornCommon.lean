import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Shared finite-disorder Born algebra

This module owns algebra common to retarded and advanced first-Born closures. It keeps the
retarded and advanced physical specializations as sibling modules while centralizing centered
first-order cancellation, side-indexed Born self-energy and second-order Green truncation data, the
exact second-order remainder, and the retained Born closure error/hypothesis.

The exact second-order remainder keeps the side-dependent noncommutative orientation inherited from
the exact configuration Dyson identities, while the R/A pair is tied together by adjunction.
Conventional retarded/advanced physical names remain in the sibling specialization modules. No
self-consistency, Dyson-resummed Born Green operator, vertex correction, Ward identity,
trace-per-volume construction, or thermodynamic limit is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Centered disorder kills every first-order insertion between fixed bounded operators. -/
theorem operatorAverage_mul_impurity_mul_eq_zero
    (hcentered : ensemble.IsCentered)
    (left right : H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω =>
      left * (ensemble.impurityPotential ω).1 * right) = 0 := by
  rw [operatorAverage_mul_left_right ensemble]
  change ensemble.operatorAverage (fun ω => (ensemble.impurityPotential ω).1) = 0 at hcentered
  rw [hcentered]
  simp

/-- Average a configuration-wise second-order expansion after its first-order contribution has
vanished. This is the R/A-neutral algebra used by both first-Born specializations. -/
theorem operatorAverage_eq_free_add_remainder_of_secondOrder
    (free : H →L[ℂ] H)
    (response firstOrder remainder : Ω → H →L[ℂ] H)
    (hexpansion : ∀ ω, response ω = (free + firstOrder ω) + remainder ω)
    (hfirst : ensemble.operatorAverage firstOrder = 0) :
    ensemble.operatorAverage response = free + ensemble.operatorAverage remainder := by
  calc
    ensemble.operatorAverage response =
        ensemble.operatorAverage (fun ω => (free + firstOrder ω) + remainder ω) := by
      apply congrArg ensemble.operatorAverage
      funext ω
      exact hexpansion ω
    _ = ensemble.operatorAverage (fun ω => free + firstOrder ω) +
        ensemble.operatorAverage remainder := by
      rw [operatorAverage_add ensemble]
    _ = (ensemble.operatorAverage (fun _ => free) +
          ensemble.operatorAverage firstOrder) +
        ensemble.operatorAverage remainder := by
      rw [operatorAverage_add ensemble]
    _ = free + ensemble.operatorAverage remainder := by
      rw [operatorAverage_const ensemble, hfirst]
      simp

/-- Exact averaged second-order Dyson remainder on either spectral side. The multiplication order is
that of the exact configuration Dyson expansion on the selected side. -/
noncomputable def exactSecondOrderRemainder
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  match side with
  | .retarded =>
      ensemble.operatorAverage (fun ω =>
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationRetardedGreen energy broadening ω)
  | .advanced =>
      ensemble.operatorAverage (fun ω =>
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening)

@[simp]
theorem exactSecondOrderRemainder_retarded
    (energy broadening : ℝ) :
    ensemble.exactSecondOrderRemainder .retarded energy broadening =
      ensemble.operatorAverage (fun ω =>
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationRetardedGreen energy broadening ω) :=
  rfl

@[simp]
theorem exactSecondOrderRemainder_advanced
    (energy broadening : ℝ) :
    ensemble.exactSecondOrderRemainder .advanced energy broadening =
      ensemble.operatorAverage (fun ω =>
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening) :=
  rfl

/-- For centered disorder, the exact averaged Green operator is the clean Green operator plus the
full exact second-order remainder on either spectral side. The selected side retains the physical
retarded-left / advanced-right remainder orientation. -/
theorem averagedGreen_eq_free_add_exactSecondOrderRemainder
    (hcentered : ensemble.IsCentered)
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.averagedGreen side energy broadening =
      ensemble.freeGreen side energy broadening +
        ensemble.exactSecondOrderRemainder side energy broadening := by
  cases side with
  | retarded =>
      simpa [averagedGreen, exactSecondOrderRemainder] using
        operatorAverage_eq_free_add_remainder_of_secondOrder
          ensemble
          (ensemble.freeGreen .retarded energy broadening)
          (fun ω => ensemble.configurationGreen .retarded energy broadening ω)
          (fun ω =>
            ensemble.freeGreen .retarded energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreen .retarded energy broadening)
          (fun ω =>
            ensemble.freeGreen .retarded energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreen .retarded energy broadening *
                  (ensemble.impurityPotential ω).1 *
                    ensemble.configurationGreen .retarded energy broadening ω)
          (configurationGreen_eq_secondOrder_add_exactRemainder_left
            ensemble .retarded energy broadening (ne_of_gt hbroadening))
          (by
            simpa using operatorAverage_mul_impurity_mul_eq_zero
              ensemble hcentered
              (ensemble.freeGreen .retarded energy broadening)
              (ensemble.freeGreen .retarded energy broadening))
  | advanced =>
      simpa [averagedGreen, exactSecondOrderRemainder] using
        operatorAverage_eq_free_add_remainder_of_secondOrder
          ensemble
          (ensemble.freeGreen .advanced energy broadening)
          (fun ω => ensemble.configurationGreen .advanced energy broadening ω)
          (fun ω =>
            ensemble.freeGreen .advanced energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreen .advanced energy broadening)
          (fun ω =>
            ensemble.configurationGreen .advanced energy broadening ω *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreen .advanced energy broadening *
                  (ensemble.impurityPotential ω).1 *
                    ensemble.freeGreen .advanced energy broadening)
          (configurationGreen_eq_secondOrder_add_exactRemainder_right
            ensemble .advanced energy broadening (ne_of_gt hbroadening))
          (by
            simpa using operatorAverage_mul_impurity_mul_eq_zero
              ensemble hcentered
              (ensemble.freeGreen .advanced energy broadening)
              (ensemble.freeGreen .advanced energy broadening))

/-- The exact advanced second-order remainder is the adjoint of the retarded remainder. -/
theorem star_exactSecondOrderRemainder_retarded
    (energy broadening : ℝ) :
    star (ensemble.exactSecondOrderRemainder .retarded energy broadening) =
      ensemble.exactSecondOrderRemainder .advanced energy broadening := by
  rw [ensemble.exactSecondOrderRemainder_retarded,
    ensemble.exactSecondOrderRemainder_advanced, ← ensemble.operatorAverage_star]
  apply congrArg ensemble.operatorAverage
  funext ω
  simp [star_mul, ensemble.star_freeRetardedGreen,
    ensemble.star_configurationRetardedGreen,
    (ensemble.impurityPotential ω).2.star_eq, mul_assoc]

/-- Side-indexed first-Born self-energy: the exact finite second moment evaluated on the clean
spectral-side Green operator. This definition does not require centered disorder. -/
noncomputable def bornSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondMoment (ensemble.freeGreen side energy broadening)

/-- The side-indexed Born self-energy is the exact finite second moment with the corresponding
clean spectral-side propagator. -/
theorem bornSelfEnergy_eq_secondMoment
    (side : SpectralSide) (energy broadening : ℝ) :
    ensemble.bornSelfEnergy side energy broadening =
      ensemble.exactSecondMoment (ensemble.freeGreen side energy broadening) :=
  rfl

/-- The advanced first-Born self-energy is the adjoint of the retarded first-Born self-energy. -/
theorem star_bornSelfEnergy_retarded
    (energy broadening : ℝ) :
    star (ensemble.bornSelfEnergy .retarded energy broadening) =
      ensemble.bornSelfEnergy .advanced energy broadening := by
  calc
    star (ensemble.bornSelfEnergy .retarded energy broadening) =
        star (ensemble.exactSecondMoment
          (ensemble.freeGreen .retarded energy broadening)) := rfl
    _ = ensemble.exactSecondMoment
        (star (ensemble.freeGreen .retarded energy broadening)) :=
      (ensemble.exactSecondMoment_star
        (ensemble.freeGreen .retarded energy broadening)).symm
    _ = ensemble.exactSecondMoment
        (ensemble.freeGreen .advanced energy broadening) := by
      rw [ensemble.freeGreen_retarded, ensemble.freeGreen_advanced,
        ensemble.star_freeRetardedGreen]
    _ = ensemble.bornSelfEnergy .advanced energy broadening := rfl

omit [CompleteSpace H] in
/-- R/A-neutral second-order Born Green expression `G₀ + G₀ Σ G₀` for supplied inputs. -/
noncomputable def secondOrderBornGreenExpression
    (freeGreen selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  freeGreen + freeGreen * selfEnergy * freeGreen

/-- Adjointing the R/A-neutral second-order Born Green expression adjoints its free Green operator
and self-energy. The symmetric `G₀ Σ G₀` placement restores the original multiplication order. -/
theorem star_secondOrderBornGreenExpression
    (freeGreen selfEnergy : H →L[ℂ] H) :
    star (secondOrderBornGreenExpression freeGreen selfEnergy) =
      secondOrderBornGreenExpression (star freeGreen) (star selfEnergy) := by
  unfold secondOrderBornGreenExpression
  simp only [star_add, star_mul, mul_assoc]

/-- Side-indexed second-order Born Green truncation `G₀ˢ + G₀ˢ Σᴮˢ G₀ˢ`.

This is the explicit second-order truncation of the Dyson series using `bornSelfEnergy`; it is not a
Dyson-resummed Green operator and is not asserted to satisfy `IsSelfEnergy`. -/
noncomputable def secondOrderBornGreen
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  secondOrderBornGreenExpression
    (ensemble.freeGreen side energy broadening)
    (ensemble.bornSelfEnergy side energy broadening)

/-- The advanced second-order Born Green truncation is the adjoint of the retarded one. -/
theorem star_secondOrderBornGreen_retarded
    (energy broadening : ℝ) :
    star (ensemble.secondOrderBornGreen .retarded energy broadening) =
      ensemble.secondOrderBornGreen .advanced energy broadening := by
  unfold secondOrderBornGreen
  rw [star_secondOrderBornGreenExpression]
  rw [ensemble.star_bornSelfEnergy_retarded]
  rw [ensemble.freeGreen_retarded, ensemble.freeGreen_advanced,
    ensemble.star_freeRetardedGreen]

omit [CompleteSpace H] in
/-- R/A-neutral closure error between an exact second-order remainder and `G₀ Σ G₀`. -/
noncomputable def secondOrderBornClosureError
    (freeGreen exactRemainder selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  exactRemainder - freeGreen * selfEnergy * freeGreen

/-- Adjointing the R/A-neutral closure error adjoints all three inputs. -/
theorem star_secondOrderBornClosureError
    (freeGreen exactRemainder selfEnergy : H →L[ℂ] H) :
    star (secondOrderBornClosureError freeGreen exactRemainder selfEnergy) =
      secondOrderBornClosureError (star freeGreen) (star exactRemainder) (star selfEnergy) := by
  unfold secondOrderBornClosureError
  simp only [star_sub, star_mul, mul_assoc]

/-- Side-indexed exact closure error between the full second-order Dyson remainder and the
Born-truncated insertion. No smallness or vanishing is assumed. -/
noncomputable def bornClosureError
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  secondOrderBornClosureError
    (ensemble.freeGreen side energy broadening)
    (ensemble.exactSecondOrderRemainder side energy broadening)
    (ensemble.bornSelfEnergy side energy broadening)

/-- The advanced exact Born closure error is the adjoint of the retarded closure error. -/
theorem star_bornClosureError_retarded
    (energy broadening : ℝ) :
    star (ensemble.bornClosureError .retarded energy broadening) =
      ensemble.bornClosureError .advanced energy broadening := by
  unfold bornClosureError
  rw [star_secondOrderBornClosureError]
  rw [ensemble.star_exactSecondOrderRemainder_retarded,
    ensemble.star_bornSelfEnergy_retarded]
  rw [ensemble.freeGreen_retarded, ensemble.freeGreen_advanced,
    ensemble.star_freeRetardedGreen]

/-- Explicit side-indexed closure hypothesis required before identifying the exact averaged Green
operator with the second-order Born Green truncation. -/
structure BornClosureHypothesis
    (side : SpectralSide) (energy broadening : ℝ) : Prop where
  closureError_eq_zero :
    ensemble.bornClosureError side energy broadening = 0

/-- A retarded Born closure hypothesis automatically gives the advanced closure hypothesis by
adjunction. -/
theorem BornClosureHypothesis.toAdvanced
    {energy broadening : ℝ}
    (closure : ensemble.BornClosureHypothesis .retarded energy broadening) :
    ensemble.BornClosureHypothesis .advanced energy broadening := by
  constructor
  have hstar := congrArg
    (fun operator : H →L[ℂ] H => star operator)
    closure.closureError_eq_zero
  have hzero : star (ensemble.bornClosureError .retarded energy broadening) = 0 := by
    simpa using hstar
  rw [ensemble.star_bornClosureError_retarded] at hzero
  exact hzero

omit [CompleteSpace H] in
/-- Adding an exact second-order remainder equals the named second-order Born Green truncation plus
the retained closure error. No smallness or vanishing of the error is assumed. -/
theorem free_add_remainder_eq_secondOrderBornGreen_add_error
    (freeGreen exactRemainder selfEnergy : H →L[ℂ] H) :
    freeGreen + exactRemainder =
      secondOrderBornGreenExpression freeGreen selfEnergy +
        secondOrderBornClosureError freeGreen exactRemainder selfEnergy := by
  unfold secondOrderBornGreenExpression secondOrderBornClosureError
  noncomm_ring

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
