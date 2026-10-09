import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedOrder

set_option linter.style.header false

/-!
# Order chambers for mixed two-point imaginary times

The stable mixed-event order is locally constant away from pairwise event-time coincidences. This
module packages the exact combinatorial chamber relation. It depends only on the statistics-independent
mixed event order.
-/

namespace SecondQuantization
namespace Common

/-- Two interaction-time assignments lie in the same mixed-event order chamber when every strict
time comparison between external or interaction events has the same truth value. -/
def SameTwoPointOrderChamber {n : ℕ} (τ τ' : ℝ) (σ υ : Fin n → ℝ) : Prop :=
  ∀ a b : TwoPointTimedEvent n,
    twoPointTimedEventTime τ τ' σ a < twoPointTimedEventTime τ τ' σ b ↔
      twoPointTimedEventTime τ τ' υ a < twoPointTimedEventTime τ τ' υ b

@[refl]
theorem sameTwoPointOrderChamber_refl {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ' σ σ := by
  intro a b
  rfl

@[symm]
theorem SameTwoPointOrderChamber.symm {n : ℕ} {τ τ' : ℝ} {σ υ : Fin n → ℝ}
    (h : SameTwoPointOrderChamber τ τ' σ υ) :
    SameTwoPointOrderChamber τ τ' υ σ := by
  intro a b
  exact (h a b).symm

@[trans]
theorem SameTwoPointOrderChamber.trans {n : ℕ} {τ τ' : ℝ} {σ υ ξ : Fin n → ℝ}
    (hσυ : SameTwoPointOrderChamber τ τ' σ υ)
    (hυξ : SameTwoPointOrderChamber τ τ' υ ξ) :
    SameTwoPointOrderChamber τ τ' σ ξ := by
  intro a b
  exact (hσυ a b).trans (hυξ a b)

theorem orderedTwoPointTimedEventPosition_lt_iff_of_sameOrderChamber
    {n : ℕ} {τ τ' : ℝ} {σ υ : Fin n → ℝ}
    (h : SameTwoPointOrderChamber τ τ' σ υ)
    (a b : TwoPointTimedEvent n) :
    orderedTwoPointTimedEventPosition τ τ' σ a <
        orderedTwoPointTimedEventPosition τ τ' σ b ↔
      orderedTwoPointTimedEventPosition τ τ' υ a <
        orderedTwoPointTimedEventPosition τ τ' υ b := by
  rw [orderedTwoPointTimedEventPosition_lt_iff,
    orderedTwoPointTimedEventPosition_lt_iff]
  change (stableTimedEventBeforeOrEqual
      (twoPointTimedEventTime τ τ' σ) twoPointTimedEventRank a b ∧ a ≠ b) ↔
    (stableTimedEventBeforeOrEqual
      (twoPointTimedEventTime τ τ' υ) twoPointTimedEventRank a b ∧ a ≠ b)
  rw [stableTimedEventBeforeOrEqual_congr
    (twoPointTimedEventTime τ τ' σ)
    (twoPointTimedEventTime τ τ' υ) twoPointTimedEventRank h a b]

end Common
end SecondQuantization
