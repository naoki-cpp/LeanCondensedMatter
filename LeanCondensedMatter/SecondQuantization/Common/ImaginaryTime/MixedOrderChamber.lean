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

private theorem twoPointTimedEventTime_eq_iff_of_sameOrderChamber
    {n : ℕ} {τ τ' : ℝ} {σ υ : Fin n → ℝ}
    (h : SameTwoPointOrderChamber τ τ' σ υ)
    (a b : TwoPointTimedEvent n) :
    twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' σ b ↔
      twoPointTimedEventTime τ τ' υ a = twoPointTimedEventTime τ τ' υ b := by
  constructor
  · intro hab
    by_contra huv
    rcases lt_or_gt_of_ne huv with huv | huv
    · have hσ := (h a b).mpr huv
      rw [hab] at hσ
      exact (lt_irrefl _ hσ)
    · have hσ := (h b a).mpr huv
      rw [hab] at hσ
      exact (lt_irrefl _ hσ)
  · intro hab
    by_contra hσ
    rcases lt_or_gt_of_ne hσ with hσ | hσ
    · have huv := (h a b).mp hσ
      rw [hab] at huv
      exact (lt_irrefl _ huv)
    · have huv := (h b a).mp hσ
      rw [hab] at huv
      exact (lt_irrefl _ huv)

theorem twoPointTimedEventBeforeOrEqual_iff_of_sameOrderChamber
    {n : ℕ} {τ τ' : ℝ} {σ υ : Fin n → ℝ}
    (h : SameTwoPointOrderChamber τ τ' σ υ)
    (a b : TwoPointTimedEvent n) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a b ↔
      twoPointTimedEventBeforeOrEqual τ τ' υ a b := by
  unfold twoPointTimedEventBeforeOrEqual
  rw [h b a, twoPointTimedEventTime_eq_iff_of_sameOrderChamber h a b]

theorem twoPointTimedEventBefore_iff_of_sameOrderChamber
    {n : ℕ} {τ τ' : ℝ} {σ υ : Fin n → ℝ}
    (h : SameTwoPointOrderChamber τ τ' σ υ)
    (a b : TwoPointTimedEvent n) :
    twoPointTimedEventBefore τ τ' σ a b ↔
      twoPointTimedEventBefore τ τ' υ a b := by
  unfold twoPointTimedEventBefore
  rw [twoPointTimedEventBeforeOrEqual_iff_of_sameOrderChamber h a b]

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
  exact twoPointTimedEventBefore_iff_of_sameOrderChamber h a b

theorem sameTwoPointOrderChamber_iff_interaction_comparisons
    {n : ℕ} (τ τ' : ℝ) (σ υ : Fin n → ℝ) :
    SameTwoPointOrderChamber τ τ' σ υ ↔
      (∀ v w, σ v < σ w ↔ υ v < υ w) ∧
      (∀ v, σ v < τ ↔ υ v < τ) ∧
      (∀ v, τ < σ v ↔ τ < υ v) ∧
      (∀ v, σ v < τ' ↔ υ v < τ') ∧
      (∀ v, τ' < σ v ↔ τ' < υ v) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v w
      simpa [SameTwoPointOrderChamber, twoPointTimedEventTime] using
        h (Sum.inr v) (Sum.inr w)
    · intro v
      simpa [SameTwoPointOrderChamber, twoPointTimedEventTime] using
        h (Sum.inr v) (Sum.inl 0)
    · intro v
      simpa [SameTwoPointOrderChamber, twoPointTimedEventTime] using
        h (Sum.inl 0) (Sum.inr v)
    · intro v
      simpa [SameTwoPointOrderChamber, twoPointTimedEventTime] using
        h (Sum.inr v) (Sum.inl 1)
    · intro v
      simpa [SameTwoPointOrderChamber, twoPointTimedEventTime] using
        h (Sum.inl 1) (Sum.inr v)
  · rintro ⟨hii, hiτ, hτi, hiτ', hτ'i⟩ a b
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            fin_cases a <;> fin_cases b <;>
              simp [twoPointTimedEventTime, twoPointExternalTimes]
        | inr b =>
            fin_cases a
            · simpa [twoPointTimedEventTime] using hτi b
            · simpa [twoPointTimedEventTime] using hτ'i b
    | inr a =>
        cases b with
        | inl b =>
            fin_cases b
            · simpa [twoPointTimedEventTime] using hiτ a
            · simpa [twoPointTimedEventTime] using hiτ' a
        | inr b =>
            simpa [twoPointTimedEventTime] using hii a b

end Common
end SecondQuantization
