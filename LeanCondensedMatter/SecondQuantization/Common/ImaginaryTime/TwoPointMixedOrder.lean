import Mathlib

set_option linter.style.header false

/-!
# Statistics-independent mixed two-point event order

A two-point insertion contributes two distinguished external events together with `n` interaction
events. This module orders those events by decreasing imaginary time, using a deterministic stable
rank at equal times: external event `0`, external event `1`, then interaction slots in their supplied
order.

The construction is purely order-theoretic. It does not know which operators the events represent,
which statistics they obey, or which exchange factor an operator realization assigns when the two
external events are exchanged. Statistics-specific layers map the ordered events to operators and
supply any exchange prefactor separately.
-/

namespace SecondQuantization
namespace Common

/-- The event type for a two-point insertion with `n` interaction vertices: two distinguished
external events followed by the interaction slots. -/
abbrev TwoPointTimedEvent (n : ℕ) : Type := Fin 2 ⊕ Fin n

/-- The two fixed external times in their canonical external-event order. -/
def twoPointExternalTimes (τ τ' : ℝ) : Fin 2 → ℝ :=
  fun e => if e = 0 then τ else τ'

@[simp]
theorem twoPointExternalTimes_zero (τ τ' : ℝ) : twoPointExternalTimes τ τ' 0 = τ := by
  simp [twoPointExternalTimes]

@[simp]
theorem twoPointExternalTimes_one (τ τ' : ℝ) : twoPointExternalTimes τ τ' 1 = τ' := by
  simp [twoPointExternalTimes]

/-- The imaginary time attached to an external or interaction event. -/
def twoPointTimedEventTime {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    TwoPointTimedEvent n → ℝ
  | .inl e => twoPointExternalTimes τ τ' e
  | .inr v => σ v

/-- Stable equal-time rank: external events have ranks `0,1` and interaction slot `v` has rank
`2 + v`. -/
def twoPointTimedEventRank {n : ℕ} : TwoPointTimedEvent n → ℕ
  | .inl e => e
  | .inr v => 2 + v

/-- Stable non-strict event precedence: later imaginary time comes first, with the stable rank
breaking equal-time ties. -/
def twoPointTimedEventBeforeOrEqual {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) : Prop :=
  twoPointTimedEventTime τ τ' σ b < twoPointTimedEventTime τ τ' σ a ∨
    (twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' σ b ∧
      twoPointTimedEventRank a ≤ twoPointTimedEventRank b)

/-- Strict stable event precedence, obtained by excluding equality from
`twoPointTimedEventBeforeOrEqual`. -/
def twoPointTimedEventBefore {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ)
    (a b : TwoPointTimedEvent n) : Prop :=
  twoPointTimedEventBeforeOrEqual τ τ' σ a b ∧ a ≠ b

private theorem twoPointTimedEventRank_injective {n : ℕ} :
    Function.Injective (twoPointTimedEventRank : TwoPointTimedEvent n → ℕ) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          apply congrArg Sum.inl
          apply Fin.ext
          simpa [twoPointTimedEventRank] using h
      | inr b =>
          simp [twoPointTimedEventRank] at h
          omega
  | inr a =>
      cases b with
      | inl b =>
          simp [twoPointTimedEventRank] at h
          omega
      | inr b =>
          apply congrArg Sum.inr
          apply Fin.ext
          simpa [twoPointTimedEventRank] using h

private theorem twoPointTimedEventBeforeOrEqual_total {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (a b : TwoPointTimedEvent n) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a b ∨
      twoPointTimedEventBeforeOrEqual τ τ' σ b a := by
  rcases lt_trichotomy
      (twoPointTimedEventTime τ τ' σ a)
      (twoPointTimedEventTime τ τ' σ b) with hab | hab | hab
  · right
    exact Or.inl hab
  · rcases le_total (twoPointTimedEventRank a) (twoPointTimedEventRank b) with hr | hr
    · left
      exact Or.inr ⟨hab, hr⟩
    · right
      exact Or.inr ⟨hab.symm, hr⟩
  · left
    exact Or.inl hab

private theorem twoPointTimedEventBeforeOrEqual_trans {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) {a b c : TwoPointTimedEvent n}
    (hab : twoPointTimedEventBeforeOrEqual τ τ' σ a b)
    (hbc : twoPointTimedEventBeforeOrEqual τ τ' σ b c) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a c := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hbc with hbc | ⟨hbcTime, _⟩
    · exact Or.inl (lt_trans hbc hab)
    · exact Or.inl (hbcTime ▸ hab)
  · rcases hbc with hbc | ⟨hbcTime, hbcRank⟩
    · exact Or.inl (habTime ▸ hbc)
    · exact Or.inr ⟨habTime.trans hbcTime, habRank.trans hbcRank⟩

private theorem twoPointTimedEventBeforeOrEqual_antisymm {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) {a b : TwoPointTimedEvent n}
    (hab : twoPointTimedEventBeforeOrEqual τ τ' σ a b)
    (hba : twoPointTimedEventBeforeOrEqual τ τ' σ b a) :
    a = b := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hba with hba | ⟨hbaTime, _⟩
    · exact (lt_asymm hab hba).elim
    · rw [hbaTime] at hab
      exact (lt_irrefl _ hab).elim
  · rcases hba with hba | ⟨_, hbaRank⟩
    · rw [habTime] at hba
      exact (lt_irrefl _ hba).elim
    · exact twoPointTimedEventRank_injective (habRank.antisymm hbaRank)

/-- Stable comparison of two fixed events is unchanged when their two event times are unchanged. -/
theorem twoPointTimedEventBeforeOrEqual_congr {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (a b : TwoPointTimedEvent n)
    (ha : twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' υ a)
    (hb : twoPointTimedEventTime τ τ' σ b = twoPointTimedEventTime τ τ' υ b) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a b ↔
      twoPointTimedEventBeforeOrEqual τ τ' υ a b := by
  simp only [twoPointTimedEventBeforeOrEqual]
  rw [ha, hb]

/-- Interaction events in their canonical supplied slot order. -/
def twoPointInteractionEventList (n : ℕ) : List (TwoPointTimedEvent n) :=
  List.ofFn fun v : Fin n => Sum.inr v

private theorem canonicalTwoPointTimedEvents_nodup (n : ℕ) :
    ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).Nodup := by
  rw [twoPointInteractionEventList]
  change ((Sum.inl (0 : Fin 2) : TwoPointTimedEvent n) ::
    (Sum.inl (1 : Fin 2) : TwoPointTimedEvent n) ::
      List.ofFn (fun v : Fin n => (Sum.inr v : TwoPointTimedEvent n))).Nodup
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ?_⟩⟩
  · simp
  · simp
  · exact List.nodup_ofFn_ofInjective Sum.inr_injective

private theorem canonicalTwoPointTimedEvents_all_mem (n : ℕ) :
    ∀ event : TwoPointTimedEvent n,
      event ∈ [Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n := by
  intro event
  cases event with
  | inl e => fin_cases e <;> simp [twoPointInteractionEventList]
  | inr v => simp [twoPointInteractionEventList]

/-- All external and interaction events sorted by decreasing time with the stable equal-time rank. -/
noncomputable def orderedTwoPointTimedEvents {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List (TwoPointTimedEvent n) := by
  classical
  exact List.insertionSort (twoPointTimedEventBeforeOrEqual τ τ' σ)
    ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n)

@[simp]
theorem orderedTwoPointTimedEvents_length {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).length = n + 2 := by
  classical
  rw [orderedTwoPointTimedEvents, List.length_insertionSort]
  simp [twoPointInteractionEventList]

/-- Time ordering permutes, but neither duplicates nor removes, the canonical mixed events. -/
theorem orderedTwoPointTimedEvents_perm {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List.Perm (orderedTwoPointTimedEvents τ τ' σ)
      ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n) := by
  classical
  exact List.perm_insertionSort _ _

/-- The fully ordered mixed-event list is pairwise sorted by stable time precedence. -/
theorem orderedTwoPointTimedEvents_pairwise {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).Pairwise
      (twoPointTimedEventBeforeOrEqual τ τ' σ) := by
  classical
  letI : Std.Total (twoPointTimedEventBeforeOrEqual τ τ' σ) :=
    ⟨twoPointTimedEventBeforeOrEqual_total τ τ' σ⟩
  letI : IsTrans (TwoPointTimedEvent n) (twoPointTimedEventBeforeOrEqual τ τ' σ) :=
    ⟨fun _ _ _ => twoPointTimedEventBeforeOrEqual_trans τ τ' σ⟩
  exact List.pairwise_insertionSort _ _

/-- The fully ordered mixed-event list contains no duplicate events. -/
theorem orderedTwoPointTimedEvents_nodup {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (orderedTwoPointTimedEvents τ τ' σ).Nodup :=
  (orderedTwoPointTimedEvents_perm τ τ' σ).nodup_iff.mpr
    (canonicalTwoPointTimedEvents_nodup n)

/-- Every external or interaction event occurs in the fully ordered event list. -/
theorem orderedTwoPointTimedEvents_all_mem {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    ∀ event : TwoPointTimedEvent n,
      event ∈ orderedTwoPointTimedEvents τ τ' σ := by
  intro event
  exact (orderedTwoPointTimedEvents_perm τ τ' σ).symm.subset
    (canonicalTwoPointTimedEvents_all_mem n event)

/-- Exact enumeration of all mixed events by their time-ordered positions. -/
noncomputable def orderedTwoPointTimedEventEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (n + 2) ≃ TwoPointTimedEvent n :=
  (finCongr (orderedTwoPointTimedEvents_length τ τ' σ).symm).trans
    (List.Nodup.getEquivOfForallMemList
      (orderedTwoPointTimedEvents τ τ' σ)
      (orderedTwoPointTimedEvents_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ))

/-- Position occupied by one event in the fully ordered mixed-event list. -/
noncomputable def orderedTwoPointTimedEventPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (event : TwoPointTimedEvent n) : Fin (n + 2) :=
  (orderedTwoPointTimedEventEquiv τ τ' σ).symm event

@[simp]
theorem orderedTwoPointTimedEventEquiv_position {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (event : TwoPointTimedEvent n) :
    orderedTwoPointTimedEventEquiv τ τ' σ
        (orderedTwoPointTimedEventPosition τ τ' σ event) = event :=
  (orderedTwoPointTimedEventEquiv τ τ' σ).apply_symm_apply event

private theorem twoPointTimedEventBeforeOrEqual_of_position_lt {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) {a b : TwoPointTimedEvent n}
    (h : orderedTwoPointTimedEventPosition τ τ' σ a <
      orderedTwoPointTimedEventPosition τ τ' σ b) :
    twoPointTimedEventBeforeOrEqual τ τ' σ a b := by
  let l := orderedTwoPointTimedEvents τ τ' σ
  let pa : Fin l.length :=
    Fin.cast (orderedTwoPointTimedEvents_length τ τ' σ).symm
      (orderedTwoPointTimedEventPosition τ τ' σ a)
  let pb : Fin l.length :=
    Fin.cast (orderedTwoPointTimedEvents_length τ τ' σ).symm
      (orderedTwoPointTimedEventPosition τ τ' σ b)
  have hp : pa < pb := by
    simpa [pa, pb] using h
  have hrel := (orderedTwoPointTimedEvents_pairwise τ τ' σ).rel_get_of_lt hp
  have ha : l.get pa = a := by
    simpa [l, pa, orderedTwoPointTimedEventPosition,
      orderedTwoPointTimedEventEquiv] using
      (List.idxOf_get
        ((List.idxOf_lt_length_iff).2
          (orderedTwoPointTimedEvents_all_mem τ τ' σ a)))
  have hb : l.get pb = b := by
    simpa [l, pb, orderedTwoPointTimedEventPosition,
      orderedTwoPointTimedEventEquiv] using
      (List.idxOf_get
        ((List.idxOf_lt_length_iff).2
          (orderedTwoPointTimedEvents_all_mem τ τ' σ b)))
  rw [ha, hb] at hrel
  exact hrel

/-- Event-position comparison is exactly strict stable time precedence. -/
theorem orderedTwoPointTimedEventPosition_lt_iff {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (a b : TwoPointTimedEvent n) :
    orderedTwoPointTimedEventPosition τ τ' σ a <
        orderedTwoPointTimedEventPosition τ τ' σ b ↔
      twoPointTimedEventBefore τ τ' σ a b := by
  constructor
  · intro h
    refine ⟨twoPointTimedEventBeforeOrEqual_of_position_lt τ τ' σ h, ?_⟩
    intro hab
    subst b
    exact (lt_irrefl _ h)
  · rintro ⟨hab, hne⟩
    rcases lt_trichotomy
        (orderedTwoPointTimedEventPosition τ τ' σ a)
        (orderedTwoPointTimedEventPosition τ τ' σ b) with h | h | h
    · exact h
    · exact (hne ((orderedTwoPointTimedEventEquiv τ τ' σ).symm.injective h)).elim
    · have hba := twoPointTimedEventBeforeOrEqual_of_position_lt τ τ' σ h
      exact (hne (twoPointTimedEventBeforeOrEqual_antisymm τ τ' σ hab hba)).elim

/-- Relative ordered positions of two events depend only on the times of those two events. -/
theorem orderedTwoPointTimedEventPosition_lt_iff_of_eventTime_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (a b : TwoPointTimedEvent n)
    (ha : twoPointTimedEventTime τ τ' σ a = twoPointTimedEventTime τ τ' υ a)
    (hb : twoPointTimedEventTime τ τ' σ b = twoPointTimedEventTime τ τ' υ b) :
    (orderedTwoPointTimedEventPosition τ τ' σ a <
        orderedTwoPointTimedEventPosition τ τ' σ b) ↔
      (orderedTwoPointTimedEventPosition τ τ' υ a <
        orderedTwoPointTimedEventPosition τ τ' υ b) := by
  rw [orderedTwoPointTimedEventPosition_lt_iff,
    orderedTwoPointTimedEventPosition_lt_iff]
  unfold twoPointTimedEventBefore
  rw [twoPointTimedEventBeforeOrEqual_congr τ τ' σ υ a b ha hb]

end Common
end SecondQuantization
