import Mathlib

set_option linter.style.header false

/-!
# Statistics-independent mixed ordering for external insertions

An external-insertion expansion contains `2 * E` distinguished external events and `n`
interaction events. This module orders the combined finite event family by decreasing imaginary time,
using the canonical external/interaction slot order to break equal-time ties.

The construction is statistics-independent. It also exposes transport along strictly monotone
reindexings of both external and interaction slots, which is the form needed when a connected
component is compared with its ambient diagram.
-/

namespace SecondQuantization
namespace Common

/-- Timed events for an even external sector with `2 * E` external insertions and `n`
interaction vertices. -/
abbrev ExternalInsertionTimedEvent (E n : ℕ) : Type :=
  Fin (2 * E) ⊕ Fin n

/-- The imaginary time attached to an external or interaction event. -/
def externalInsertionTimedEventTime {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ExternalInsertionTimedEvent E n → ℝ
  | .inl e => externalTime e
  | .inr v => σ v

/-- Stable equal-time rank: external slots come first, followed by interaction slots. -/
def externalInsertionTimedEventRank {E n : ℕ}
    (event : ExternalInsertionTimedEvent E n) : ℕ :=
  ((finSumFinEquiv : ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)) event).val

/-- Stable non-strict event precedence: later imaginary time comes first, with the canonical rank
breaking equal-time ties. -/
def externalInsertionTimedEventBeforeOrEqual {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) : Prop :=
  externalInsertionTimedEventTime externalTime σ b <
      externalInsertionTimedEventTime externalTime σ a ∨
    (externalInsertionTimedEventTime externalTime σ a =
        externalInsertionTimedEventTime externalTime σ b ∧
      externalInsertionTimedEventRank a ≤ externalInsertionTimedEventRank b)

/-- Strict stable event precedence. -/
def externalInsertionTimedEventBefore {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) : Prop :=
  externalInsertionTimedEventBeforeOrEqual externalTime σ a b ∧ a ≠ b

private theorem externalInsertionTimedEventBeforeOrEqual_total {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) :
    externalInsertionTimedEventBeforeOrEqual externalTime σ a b ∨
      externalInsertionTimedEventBeforeOrEqual externalTime σ b a := by
  rcases lt_trichotomy
      (externalInsertionTimedEventTime externalTime σ a)
      (externalInsertionTimedEventTime externalTime σ b) with hab | hab | hab
  · right
    exact Or.inl hab
  · rcases le_total (externalInsertionTimedEventRank a)
      (externalInsertionTimedEventRank b) with hr | hr
    · left
      exact Or.inr ⟨hab, hr⟩
    · right
      exact Or.inr ⟨hab.symm, hr⟩
  · left
    exact Or.inl hab

private theorem externalInsertionTimedEventBeforeOrEqual_trans {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    {a b c : ExternalInsertionTimedEvent E n}
    (hab : externalInsertionTimedEventBeforeOrEqual externalTime σ a b)
    (hbc : externalInsertionTimedEventBeforeOrEqual externalTime σ b c) :
    externalInsertionTimedEventBeforeOrEqual externalTime σ a c := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hbc with hbc | ⟨hbcTime, _⟩
    · exact Or.inl (lt_trans hbc hab)
    · exact Or.inl (hbcTime ▸ hab)
  · rcases hbc with hbc | ⟨hbcTime, hbcRank⟩
    · exact Or.inl (habTime ▸ hbc)
    · exact Or.inr ⟨habTime.trans hbcTime, habRank.trans hbcRank⟩

private theorem externalInsertionTimedEventBeforeOrEqual_antisymm {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    {a b : ExternalInsertionTimedEvent E n}
    (hab : externalInsertionTimedEventBeforeOrEqual externalTime σ a b)
    (hba : externalInsertionTimedEventBeforeOrEqual externalTime σ b a) :
    a = b := by
  rcases hab with hab | ⟨habTime, habRank⟩
  · rcases hba with hba | ⟨hbaTime, _⟩
    · exact (lt_asymm hab hba).elim
    · rw [hbaTime] at hab
      exact (lt_irrefl _ hab).elim
  · rcases hba with hba | ⟨_, hbaRank⟩
    · rw [habTime] at hba
      exact (lt_irrefl _ hba).elim
    · apply
        (finSumFinEquiv :
          ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).injective
      apply Fin.ext
      exact habRank.antisymm hbaRank

/-- Stable comparison of two fixed events is unchanged when their event times are unchanged. -/
theorem externalInsertionTimedEventBeforeOrEqual_congr {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n)
    (ha : externalInsertionTimedEventTime externalTime σ a =
      externalInsertionTimedEventTime externalTime υ a)
    (hb : externalInsertionTimedEventTime externalTime σ b =
      externalInsertionTimedEventTime externalTime υ b) :
    externalInsertionTimedEventBeforeOrEqual externalTime σ a b ↔
      externalInsertionTimedEventBeforeOrEqual externalTime υ a b := by
  simp only [externalInsertionTimedEventBeforeOrEqual]
  rw [ha, hb]

/-- Canonical event enumeration: external slots first, then interaction slots. -/
def canonicalExternalInsertionTimedEvents (E n : ℕ) :
    List (ExternalInsertionTimedEvent E n) :=
  List.ofFn fun p : Fin (2 * E + n) =>
    (finSumFinEquiv :
      ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).symm p

private theorem canonicalExternalInsertionTimedEvents_nodup (E n : ℕ) :
    (canonicalExternalInsertionTimedEvents E n).Nodup := by
  unfold canonicalExternalInsertionTimedEvents
  exact List.nodup_ofFn_ofInjective
    ((finSumFinEquiv :
      ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).symm.injective)

private theorem canonicalExternalInsertionTimedEvents_all_mem (E n : ℕ) :
    ∀ event : ExternalInsertionTimedEvent E n,
      event ∈ canonicalExternalInsertionTimedEvents E n := by
  intro event
  rw [canonicalExternalInsertionTimedEvents, List.mem_ofFn]
  exact ⟨
    (finSumFinEquiv :
      ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)) event,
    by simp⟩

/-- All external and interaction events sorted by decreasing time with stable equal-time rank. -/
noncomputable def orderedExternalInsertionTimedEvents {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List (ExternalInsertionTimedEvent E n) := by
  classical
  exact List.insertionSort
    (externalInsertionTimedEventBeforeOrEqual externalTime σ)
    (canonicalExternalInsertionTimedEvents E n)

@[simp]
theorem orderedExternalInsertionTimedEvents_length {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).length = 2 * E + n := by
  classical
  rw [orderedExternalInsertionTimedEvents, List.length_insertionSort]
  simp [canonicalExternalInsertionTimedEvents]

/-- Time ordering permutes, but neither duplicates nor removes, the canonical mixed events. -/
theorem orderedExternalInsertionTimedEvents_perm {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List.Perm (orderedExternalInsertionTimedEvents externalTime σ)
      (canonicalExternalInsertionTimedEvents E n) := by
  classical
  exact List.perm_insertionSort _ _

/-- The fully ordered mixed-event list is pairwise sorted by stable time precedence. -/
theorem orderedExternalInsertionTimedEvents_pairwise {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Pairwise
      (externalInsertionTimedEventBeforeOrEqual externalTime σ) := by
  classical
  letI : Std.Total (externalInsertionTimedEventBeforeOrEqual externalTime σ) :=
    ⟨externalInsertionTimedEventBeforeOrEqual_total externalTime σ⟩
  letI : IsTrans (ExternalInsertionTimedEvent E n)
      (externalInsertionTimedEventBeforeOrEqual externalTime σ) :=
    ⟨fun _ _ _ =>
      externalInsertionTimedEventBeforeOrEqual_trans externalTime σ⟩
  exact List.pairwise_insertionSort _ _

/-- The fully ordered mixed-event list contains no duplicate events. -/
theorem orderedExternalInsertionTimedEvents_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Nodup :=
  (orderedExternalInsertionTimedEvents_perm externalTime σ).nodup_iff.mpr
    (canonicalExternalInsertionTimedEvents_nodup E n)

/-- Every external or interaction event occurs in the fully ordered event list. -/
theorem orderedExternalInsertionTimedEvents_all_mem {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ∀ event : ExternalInsertionTimedEvent E n,
      event ∈ orderedExternalInsertionTimedEvents externalTime σ := by
  intro event
  exact (orderedExternalInsertionTimedEvents_perm externalTime σ).symm.subset
    (canonicalExternalInsertionTimedEvents_all_mem E n event)

/-- Exact enumeration of all mixed events by their time-ordered positions. -/
noncomputable def orderedExternalInsertionTimedEventEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Fin (2 * E + n) ≃ ExternalInsertionTimedEvent E n :=
  (finCongr (orderedExternalInsertionTimedEvents_length externalTime σ).symm).trans
    (List.Nodup.getEquivOfForallMemList
      (orderedExternalInsertionTimedEvents externalTime σ)
      (orderedExternalInsertionTimedEvents_nodup externalTime σ)
      (orderedExternalInsertionTimedEvents_all_mem externalTime σ))

/-- Position occupied by one event in the fully ordered mixed-event list. -/
noncomputable def orderedExternalInsertionTimedEventPosition {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (event : ExternalInsertionTimedEvent E n) : Fin (2 * E + n) :=
  (orderedExternalInsertionTimedEventEquiv externalTime σ).symm event

@[simp]
theorem orderedExternalInsertionTimedEventEquiv_position {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (event : ExternalInsertionTimedEvent E n) :
    orderedExternalInsertionTimedEventEquiv externalTime σ
        (orderedExternalInsertionTimedEventPosition externalTime σ event) = event :=
  (orderedExternalInsertionTimedEventEquiv externalTime σ).apply_symm_apply event

private theorem externalInsertionTimedEventBeforeOrEqual_of_position_lt {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    {a b : ExternalInsertionTimedEvent E n}
    (h : orderedExternalInsertionTimedEventPosition externalTime σ a <
      orderedExternalInsertionTimedEventPosition externalTime σ b) :
    externalInsertionTimedEventBeforeOrEqual externalTime σ a b := by
  let l := orderedExternalInsertionTimedEvents externalTime σ
  let pa : Fin l.length :=
    Fin.cast (orderedExternalInsertionTimedEvents_length externalTime σ).symm
      (orderedExternalInsertionTimedEventPosition externalTime σ a)
  let pb : Fin l.length :=
    Fin.cast (orderedExternalInsertionTimedEvents_length externalTime σ).symm
      (orderedExternalInsertionTimedEventPosition externalTime σ b)
  have hp : pa < pb := by
    simpa [pa, pb] using h
  have hrel :=
    (orderedExternalInsertionTimedEvents_pairwise externalTime σ).rel_get_of_lt hp
  have ha : l.get pa = a := by
    simpa [l, pa, orderedExternalInsertionTimedEventPosition,
      orderedExternalInsertionTimedEventEquiv] using
      (List.idxOf_get
        ((List.idxOf_lt_length_iff).2
          (orderedExternalInsertionTimedEvents_all_mem externalTime σ a)))
  have hb : l.get pb = b := by
    simpa [l, pb, orderedExternalInsertionTimedEventPosition,
      orderedExternalInsertionTimedEventEquiv] using
      (List.idxOf_get
        ((List.idxOf_lt_length_iff).2
          (orderedExternalInsertionTimedEvents_all_mem externalTime σ b)))
  rw [ha, hb] at hrel
  exact hrel

/-- Event-position comparison is exactly strict stable time precedence. -/
theorem orderedExternalInsertionTimedEventPosition_lt_iff {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) :
    orderedExternalInsertionTimedEventPosition externalTime σ a <
        orderedExternalInsertionTimedEventPosition externalTime σ b ↔
      externalInsertionTimedEventBefore externalTime σ a b := by
  constructor
  · intro h
    refine ⟨
      externalInsertionTimedEventBeforeOrEqual_of_position_lt externalTime σ h,
      ?_⟩
    intro hab
    subst b
    exact (lt_irrefl _ h)
  · rintro ⟨hab, hne⟩
    rcases lt_trichotomy
        (orderedExternalInsertionTimedEventPosition externalTime σ a)
        (orderedExternalInsertionTimedEventPosition externalTime σ b) with h | h | h
    · exact h
    · exact
        (hne
          ((orderedExternalInsertionTimedEventEquiv externalTime σ).symm.injective h)).elim
    · have hba :=
        externalInsertionTimedEventBeforeOrEqual_of_position_lt externalTime σ h
      exact
        (hne
          (externalInsertionTimedEventBeforeOrEqual_antisymm
            externalTime σ hab hba)).elim

/-- Relative ordered positions of two events depend only on the times of those two events. -/
theorem orderedExternalInsertionTimedEventPosition_lt_iff_of_eventTime_eq {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n)
    (ha : externalInsertionTimedEventTime externalTime σ a =
      externalInsertionTimedEventTime externalTime υ a)
    (hb : externalInsertionTimedEventTime externalTime σ b =
      externalInsertionTimedEventTime externalTime υ b) :
    (orderedExternalInsertionTimedEventPosition externalTime σ a <
        orderedExternalInsertionTimedEventPosition externalTime σ b) ↔
      (orderedExternalInsertionTimedEventPosition externalTime υ a <
        orderedExternalInsertionTimedEventPosition externalTime υ b) := by
  rw [orderedExternalInsertionTimedEventPosition_lt_iff,
    orderedExternalInsertionTimedEventPosition_lt_iff]
  unfold externalInsertionTimedEventBefore
  rw [externalInsertionTimedEventBeforeOrEqual_congr
    externalTime σ υ a b ha hb]

variable {E₁ E₂ m n : ℕ}

/-- Transport a mixed event along external- and interaction-slot reindexings. -/
def externalInsertionTimedEventMap
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n) :
    ExternalInsertionTimedEvent E₁ m → ExternalInsertionTimedEvent E₂ n :=
  Sum.map externalMap interactionMap

@[simp]
theorem externalInsertionTimedEventMap_inl
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n) (e : Fin (2 * E₁)) :
    externalInsertionTimedEventMap externalMap interactionMap (Sum.inl e) =
      Sum.inl (externalMap e) :=
  rfl

@[simp]
theorem externalInsertionTimedEventMap_inr
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n) (v : Fin m) :
    externalInsertionTimedEventMap externalMap interactionMap (Sum.inr v) =
      Sum.inr (interactionMap v) :=
  rfl

theorem externalInsertionTimedEventMap_injective
    {externalMap : Fin (2 * E₁) → Fin (2 * E₂)}
    {interactionMap : Fin m → Fin n}
    (hExternal : Function.Injective externalMap)
    (hInteraction : Function.Injective interactionMap) :
    Function.Injective
      (externalInsertionTimedEventMap externalMap interactionMap) := by
  simpa [externalInsertionTimedEventMap] using
    (Sum.map_injective.mpr ⟨hExternal, hInteraction⟩)

@[simp]
theorem externalInsertionTimedEventTime_map
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventTime externalTime σ
        (externalInsertionTimedEventMap externalMap interactionMap a) =
      externalInsertionTimedEventTime (externalTime ∘ externalMap)
        (σ ∘ interactionMap) a := by
  cases a <;> rfl

theorem externalInsertionTimedEventRank_map_le_iff
    {externalMap : Fin (2 * E₁) → Fin (2 * E₂)}
    {interactionMap : Fin m → Fin n}
    (hExternal : StrictMono externalMap)
    (hInteraction : StrictMono interactionMap)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventRank
        (externalInsertionTimedEventMap externalMap interactionMap a) ≤
        externalInsertionTimedEventRank
          (externalInsertionTimedEventMap externalMap interactionMap b) ↔
      externalInsertionTimedEventRank a ≤ externalInsertionTimedEventRank b := by
  have hExternalLe :
      ∀ x y : Fin (2 * E₁),
        ((externalMap x : ℕ) ≤ (externalMap y : ℕ)) ↔
          ((x : ℕ) ≤ (y : ℕ)) := by
    intro x y
    rw [← Fin.le_def, ← Fin.le_def]
    exact hExternal.le_iff_le
  have hInteractionLe :
      ∀ x y : Fin m,
        ((interactionMap x : ℕ) ≤ (interactionMap y : ℕ)) ↔
          ((x : ℕ) ≤ (y : ℕ)) := by
    intro x y
    rw [← Fin.le_def, ← Fin.le_def]
    exact hInteraction.le_iff_le
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          simpa [externalInsertionTimedEventRank] using hExternalLe a b
      | inr w =>
          have ha := a.isLt
          have hw := w.isLt
          simp [externalInsertionTimedEventRank] <;> omega
  | inr v =>
      cases b with
      | inl b =>
          have hv := v.isLt
          have hb := b.isLt
          simp [externalInsertionTimedEventRank] <;> omega
      | inr w =>
          simpa [externalInsertionTimedEventRank] using hInteractionLe v w

theorem externalInsertionTimedEventBeforeOrEqual_map_iff
    {externalMap : Fin (2 * E₁) → Fin (2 * E₂)}
    {interactionMap : Fin m → Fin n}
    (hExternal : StrictMono externalMap)
    (hInteraction : StrictMono interactionMap)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventBeforeOrEqual externalTime σ
        (externalInsertionTimedEventMap externalMap interactionMap a)
        (externalInsertionTimedEventMap externalMap interactionMap b) ↔
      externalInsertionTimedEventBeforeOrEqual
        (externalTime ∘ externalMap) (σ ∘ interactionMap) a b := by
  simp only [externalInsertionTimedEventBeforeOrEqual,
    externalInsertionTimedEventTime_map]
  rw [externalInsertionTimedEventRank_map_le_iff hExternal hInteraction]

theorem externalInsertionTimedEventBefore_map_iff
    {externalMap : Fin (2 * E₁) → Fin (2 * E₂)}
    {interactionMap : Fin m → Fin n}
    (hExternal : StrictMono externalMap)
    (hInteraction : StrictMono interactionMap)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventBefore externalTime σ
        (externalInsertionTimedEventMap externalMap interactionMap a)
        (externalInsertionTimedEventMap externalMap interactionMap b) ↔
      externalInsertionTimedEventBefore
        (externalTime ∘ externalMap) (σ ∘ interactionMap) a b := by
  simp only [externalInsertionTimedEventBefore]
  rw [externalInsertionTimedEventBeforeOrEqual_map_iff
    hExternal hInteraction]
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab =>
      hne (congrArg
        (externalInsertionTimedEventMap externalMap interactionMap) hab)⟩
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab =>
      hne
        (externalInsertionTimedEventMap_injective
          hExternal.injective hInteraction.injective hab)⟩

theorem orderedExternalInsertionTimedEventPosition_map_lt_iff
    {externalMap : Fin (2 * E₁) → Fin (2 * E₂)}
    {interactionMap : Fin m → Fin n}
    (hExternal : StrictMono externalMap)
    (hInteraction : StrictMono interactionMap)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    orderedExternalInsertionTimedEventPosition externalTime σ
        (externalInsertionTimedEventMap externalMap interactionMap a) <
        orderedExternalInsertionTimedEventPosition externalTime σ
          (externalInsertionTimedEventMap externalMap interactionMap b) ↔
      orderedExternalInsertionTimedEventPosition
          (externalTime ∘ externalMap) (σ ∘ interactionMap) a <
        orderedExternalInsertionTimedEventPosition
          (externalTime ∘ externalMap) (σ ∘ interactionMap) b := by
  rw [orderedExternalInsertionTimedEventPosition_lt_iff,
    orderedExternalInsertionTimedEventPosition_lt_iff,
    externalInsertionTimedEventBefore_map_iff hExternal hInteraction]

end Common
end SecondQuantization
