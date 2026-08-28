import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Shared finite-disorder Born algebra

This module owns algebra common to retarded and advanced first-Born closures. It keeps the
retarded and advanced physical specializations as sibling modules while centralizing centered
first-order cancellation, the side-indexed Born self-energy and resolvent approximation, second-order
finite averaging, and the R/A-neutral second-order Born approximation/error formulas.

Orientation-sensitive Dyson remainders and physical closure hypotheses remain in their
specialization modules. No self-consistency, vertex correction, Ward identity, trace-per-volume
construction, or thermodynamic limit is introduced here.
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

omit [CompleteSpace H] in
/-- R/A-neutral second-order Born resolvent expression `G₀ + G₀ Σ G₀`. -/
noncomputable def secondOrderBornResolventApproximation
    (freeGreen selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  freeGreen + freeGreen * selfEnergy * freeGreen

/-- Side-indexed second-order Born approximation `G₀ˢ + G₀ˢ Σˢ G₀ˢ`. -/
noncomputable def bornResolventApproximation
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  secondOrderBornResolventApproximation
    (ensemble.freeGreen side energy broadening)
    (ensemble.bornSelfEnergy side energy broadening)

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
