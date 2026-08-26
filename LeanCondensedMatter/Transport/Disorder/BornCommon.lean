import LeanCondensedMatter.Transport.Disorder.Moments
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Shared finite-disorder Born algebra

This module owns algebra common to retarded and advanced first-Born closures. It keeps the
retarded and advanced physical specializations as sibling modules while centralizing centered
first-order cancellation, second-order finite averaging, and the R/A-neutral second-order Born
approximation/error formulas.

Orientation-sensitive Dyson remainders, retarded/advanced self-energies, and physical closure
hypotheses remain in their specialization modules. No resolvent choice, self-consistency, vertex
correction, Ward identity, trace-per-volume construction, or thermodynamic limit is introduced here.
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

omit [CompleteSpace H] in
/-- R/A-neutral second-order Born resolvent expression `G₀ + G₀ Σ G₀`. -/
noncomputable def secondOrderBornResolventApproximation
    (freeGreen selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  freeGreen + freeGreen * selfEnergy * freeGreen

omit [CompleteSpace H] in
/-- R/A-neutral closure error between an exact second-order remainder and `G₀ Σ G₀`. -/
noncomputable def secondOrderBornClosureError
    (freeGreen exactRemainder selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  exactRemainder - freeGreen * selfEnergy * freeGreen

omit [CompleteSpace H] in
/-- Adding an exact second-order remainder equals the Born-truncated expression plus the retained
closure error. No smallness or vanishing of the error is assumed. -/
theorem free_add_remainder_eq_bornApproximation_add_error
    (freeGreen exactRemainder selfEnergy : H →L[ℂ] H) :
    freeGreen + exactRemainder =
      secondOrderBornResolventApproximation freeGreen selfEnergy +
        secondOrderBornClosureError freeGreen exactRemainder selfEnergy := by
  unfold secondOrderBornResolventApproximation secondOrderBornClosureError
  noncomm_ring

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
