import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.Combinatorics.ListFlatMapOrder
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Mixed-time order for arbitrary external insertions

This module provides only the ordering data needed by the higher-point fermionic consumer:

* sort the `2 * E` external events together with `n` interaction events by imaginary time;
* expand that event order to the corresponding atomic legs;
* identify the time-ordered atomic positions with the fixed flattened
  `ExternalInsertionDiagram` positions.

The component-amplitude factorization also needs the corresponding restriction theorem: strictly
monotone reindexings of external and interaction slots preserve the induced mixed atomic order.
That transport remains purely order-theoretic and statistics-independent.
-/

namespace SecondQuantization
namespace Common

/-- Timed events for `2 * E` external insertions and `n` interaction vertices. -/
abbrev ExternalInsertionTimedEvent (E n : ℕ) : Type :=
  Fin (2 * E) ⊕ Fin n

/-- The imaginary time carried by an external or interaction event. -/
def externalInsertionTimedEventTime {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ExternalInsertionTimedEvent E n → ℝ
  | .inl e => externalTime e
  | .inr v => σ v

def externalInsertionTimedEventRank {E n : ℕ}
    (event : ExternalInsertionTimedEvent E n) : ℕ :=
  ((finSumFinEquiv : ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)) event).val

def externalInsertionTimedEventBeforeOrEqual {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) : Prop :=
  externalInsertionTimedEventTime externalTime σ b <
      externalInsertionTimedEventTime externalTime σ a ∨
    (externalInsertionTimedEventTime externalTime σ a =
        externalInsertionTimedEventTime externalTime σ b ∧
      externalInsertionTimedEventRank a ≤ externalInsertionTimedEventRank b)

/-- Strict stable event precedence, obtained by excluding equality from the non-strict order. -/
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
    · apply (finSumFinEquiv : ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)).injective
      apply Fin.ext
      exact habRank.antisymm hbaRank

private def canonicalExternalInsertionTimedEvents (E n : ℕ) :
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

/-- All external and interaction events sorted by decreasing imaginary time.
Equal-time events use the fixed flattened external-first rank. -/
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
  rw [orderedExternalInsertionTimedEvents, List.length_insertionSort,
    canonicalExternalInsertionTimedEvents]
  simp

theorem orderedExternalInsertionTimedEvents_perm {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List.Perm (orderedExternalInsertionTimedEvents externalTime σ)
      (canonicalExternalInsertionTimedEvents E n) := by
  classical
  exact List.perm_insertionSort _ _

theorem orderedExternalInsertionTimedEvents_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Nodup :=
  (orderedExternalInsertionTimedEvents_perm externalTime σ).nodup_iff.mpr
    (canonicalExternalInsertionTimedEvents_nodup E n)

theorem orderedExternalInsertionTimedEvents_all_mem {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ∀ event : ExternalInsertionTimedEvent E n,
      event ∈ orderedExternalInsertionTimedEvents externalTime σ := by
  intro event
  exact (orderedExternalInsertionTimedEvents_perm externalTime σ).symm.subset
    (canonicalExternalInsertionTimedEvents_all_mem E n event)

/-- The fully ordered event list is pairwise sorted by stable time precedence. -/
theorem orderedExternalInsertionTimedEvents_pairwise {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Pairwise
      (externalInsertionTimedEventBeforeOrEqual externalTime σ) := by
  classical
  letI : Std.Total (externalInsertionTimedEventBeforeOrEqual externalTime σ) :=
    ⟨externalInsertionTimedEventBeforeOrEqual_total externalTime σ⟩
  letI : IsTrans (ExternalInsertionTimedEvent E n)
      (externalInsertionTimedEventBeforeOrEqual externalTime σ) :=
    ⟨fun _ _ _ => externalInsertionTimedEventBeforeOrEqual_trans externalTime σ⟩
  exact List.pairwise_insertionSort _ _

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
  have hrel := (orderedExternalInsertionTimedEvents_pairwise externalTime σ).rel_get_of_lt hp
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
    refine ⟨externalInsertionTimedEventBeforeOrEqual_of_position_lt externalTime σ h, ?_⟩
    intro hab
    subst b
    exact (lt_irrefl _ h)
  · rintro ⟨hab, hne⟩
    rcases lt_trichotomy
        (orderedExternalInsertionTimedEventPosition externalTime σ a)
        (orderedExternalInsertionTimedEventPosition externalTime σ b) with h | h | h
    · exact h
    · exact (hne ((orderedExternalInsertionTimedEventEquiv externalTime σ).symm.injective h)).elim
    · have hba := externalInsertionTimedEventBeforeOrEqual_of_position_lt externalTime σ h
      exact (hne
        (externalInsertionTimedEventBeforeOrEqual_antisymm externalTime σ hab hba)).elim

/-- The standard external-insertion leg type with `n` ordered interaction slots. -/
abbrev OrderedExternalInsertionLeg (E n : ℕ) : Type :=
  ExternalInsertionLeg E (Finset.univ : Finset (Fin n))

/-- Atomic legs contributed by one mixed event. -/
def externalInsertionTimedEventAtomicLegs {E n : ℕ} :
    ExternalInsertionTimedEvent E n → List (OrderedExternalInsertionLeg E n)
  | .inl e => [Sum.inl e]
  | .inr v => List.ofFn fun l : Fin 4 =>
      Sum.inr (⟨v, Finset.mem_univ v⟩, l)

/-- Atomic leg identities in mixed-time event order. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegs {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List (OrderedExternalInsertionLeg E n) :=
  (orderedExternalInsertionTimedEvents externalTime σ).flatMap
    externalInsertionTimedEventAtomicLegs

private theorem externalInsertionTimedEventAtomicLegs_nodup {E n : ℕ}
    (event : ExternalInsertionTimedEvent E n) :
    (externalInsertionTimedEventAtomicLegs event).Nodup := by
  cases event with
  | inl e => simp [externalInsertionTimedEventAtomicLegs]
  | inr v =>
      rw [externalInsertionTimedEventAtomicLegs]
      apply List.nodup_ofFn_ofInjective
      intro a b h
      exact congrArg Prod.snd (Sum.inr.inj h)

private theorem externalInsertionTimedEventAtomicLegs_disjoint {E n : ℕ}
    {a b : ExternalInsertionTimedEvent E n} (h : a ≠ b) :
    List.Disjoint (externalInsertionTimedEventAtomicLegs a)
      (externalInsertionTimedEventAtomicLegs b) := by
  cases a with
  | inl e =>
      cases b with
      | inl e' => simpa [externalInsertionTimedEventAtomicLegs] using h.symm
      | inr v => simp [externalInsertionTimedEventAtomicLegs]
  | inr v =>
      cases b with
      | inl e => simp [externalInsertionTimedEventAtomicLegs]
      | inr v' =>
          have hv : v ≠ v' := by
            intro hv
            apply h
            cases hv
            rfl
          simpa [externalInsertionTimedEventAtomicLegs] using hv.symm

private theorem externalInsertionMixedTimeOrderedAtomicLegs_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).Nodup := by
  rw [externalInsertionMixedTimeOrderedAtomicLegs, List.nodup_flatMap]
  refine ⟨
    fun event _ => externalInsertionTimedEventAtomicLegs_nodup event,
    ?_⟩
  exact
    (orderedExternalInsertionTimedEvents_nodup externalTime σ).pairwise_of_forall_ne
      (fun _ _ _ _ h => externalInsertionTimedEventAtomicLegs_disjoint h)

private theorem externalInsertionMixedTimeOrderedAtomicLegs_all_mem {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ∀ leg : OrderedExternalInsertionLeg E n,
      leg ∈ externalInsertionMixedTimeOrderedAtomicLegs externalTime σ := by
  intro leg
  rw [externalInsertionMixedTimeOrderedAtomicLegs, List.mem_flatMap]
  cases leg with
  | inl e =>
      exact ⟨
        Sum.inl e,
        orderedExternalInsertionTimedEvents_all_mem externalTime σ (Sum.inl e),
        by simp [externalInsertionTimedEventAtomicLegs]⟩
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      refine ⟨
        Sum.inr v,
        orderedExternalInsertionTimedEvents_all_mem externalTime σ (Sum.inr v),
        ?_⟩
      rw [externalInsertionTimedEventAtomicLegs, List.mem_ofFn]
      exact ⟨l, rfl⟩

private theorem externalInsertionMixedTimeOrderedAtomicLegs_length {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).length =
      2 * (2 * n + E) := by
  let l := externalInsertionMixedTimeOrderedAtomicLegs externalTime σ
  have hcard :
      l.length = Fintype.card (OrderedExternalInsertionLeg E n) := by
    simpa using
      Fintype.card_congr
        (List.Nodup.getEquivOfForallMemList l
          (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
          (externalInsertionMixedTimeOrderedAtomicLegs_all_mem externalTime σ))
  rw [hcard]
  simp [OrderedExternalInsertionLeg]
  omega

/-- Exact bijection from mixed-time atomic positions to canonical external-insertion legs. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + E)) ≃ OrderedExternalInsertionLeg E n :=
  (finCongr
    (externalInsertionMixedTimeOrderedAtomicLegs_length externalTime σ).symm).trans
    (List.Nodup.getEquivOfForallMemList
      (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ)
      (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
      (externalInsertionMixedTimeOrderedAtomicLegs_all_mem externalTime σ))

/-- The mixed event supporting one canonical external-insertion leg. -/
def orderedExternalInsertionLegEvent {E n : ℕ} :
    OrderedExternalInsertionLeg E n → ExternalInsertionTimedEvent E n
  | .inl e => .inl e
  | .inr p => .inr p.1.1

/-- Every canonical leg belongs to the local atomic-leg list of its supporting event. -/
theorem orderedExternalInsertionLeg_mem_eventAtomicLegs {E n : ℕ}
    (leg : OrderedExternalInsertionLeg E n) :
    leg ∈ externalInsertionTimedEventAtomicLegs (orderedExternalInsertionLegEvent leg) := by
  cases leg with
  | inl e => simp [orderedExternalInsertionLegEvent, externalInsertionTimedEventAtomicLegs]
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      rw [orderedExternalInsertionLegEvent, externalInsertionTimedEventAtomicLegs, List.mem_ofFn]
      exact ⟨l, rfl⟩

/-- The mixed position occupied by a canonical external-insertion leg identity. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegPosition {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) : Fin (2 * (2 * n + E)) := by
  classical
  letI : BEq (OrderedExternalInsertionLeg E n) := instBEqOfDecidableEq
  refine ⟨(externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).idxOf leg, ?_⟩
  rw [← externalInsertionMixedTimeOrderedAtomicLegs_length externalTime σ]
  exact List.idxOf_lt_length_iff.mpr
    (externalInsertionMixedTimeOrderedAtomicLegs_all_mem externalTime σ leg)

@[simp]
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_equiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + E))) :
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p) = p := by
  exact (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm_apply_apply p

@[simp]
theorem externalInsertionMixedTimeOrderedAtomicLegEquiv_position {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) = leg := by
  exact (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).apply_symm_apply leg

private theorem externalInsertionMixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt
    {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E n)
    (hEvent : orderedExternalInsertionTimedEventPosition externalTime σ
        (orderedExternalInsertionLegEvent x) <
      orderedExternalInsertionTimedEventPosition externalTime σ
        (orderedExternalInsertionLegEvent y)) :
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ x <
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ y := by
  classical
  letI : BEq (ExternalInsertionTimedEvent E n) := instBEqOfDecidableEq
  letI : BEq (OrderedExternalInsertionLeg E n) := instBEqOfDecidableEq
  have hEventIdx :
      (orderedExternalInsertionTimedEvents externalTime σ).idxOf
          (orderedExternalInsertionLegEvent x) <
        (orderedExternalInsertionTimedEvents externalTime σ).idxOf
          (orderedExternalInsertionLegEvent y) := by
    simpa [orderedExternalInsertionTimedEventPosition,
      orderedExternalInsertionTimedEventEquiv,
      List.Nodup.getEquivOfForallMemList] using hEvent
  have h := List.idxOf_flatMap_lt_of_idxOf_lt externalInsertionTimedEventAtomicLegs
    (orderedExternalInsertionTimedEvents externalTime σ)
    (orderedExternalInsertionLegEvent x) (orderedExternalInsertionLegEvent y) x y
    (orderedExternalInsertionTimedEvents_nodup externalTime σ)
    (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
    (orderedExternalInsertionTimedEvents_all_mem externalTime σ
      (orderedExternalInsertionLegEvent x))
    (orderedExternalInsertionTimedEvents_all_mem externalTime σ
      (orderedExternalInsertionLegEvent y))
    (orderedExternalInsertionLeg_mem_eventAtomicLegs x)
    (orderedExternalInsertionLeg_mem_eventAtomicLegs y) hEventIdx
  simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
    externalInsertionMixedTimeOrderedAtomicLegs] using h

private theorem externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
    {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E n)
    (hxy : orderedExternalInsertionLegEvent x ≠ orderedExternalInsertionLegEvent y) :
    (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ x <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ y) ↔
      (orderedExternalInsertionTimedEventPosition externalTime σ
        (orderedExternalInsertionLegEvent x) <
       orderedExternalInsertionTimedEventPosition externalTime σ
        (orderedExternalInsertionLegEvent y)) := by
  constructor
  · intro hLeg
    rcases lt_trichotomy
        (orderedExternalInsertionTimedEventPosition externalTime σ
          (orderedExternalInsertionLegEvent x))
        (orderedExternalInsertionTimedEventPosition externalTime σ
          (orderedExternalInsertionLegEvent y)) with hEvent | hEvent | hEvent
    · exact hEvent
    · exact (hxy
        ((orderedExternalInsertionTimedEventEquiv externalTime σ).symm.injective hEvent)).elim
    · have hReverse :=
        externalInsertionMixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt
          externalTime σ y x hEvent
      exact (lt_asymm hLeg hReverse).elim
  · exact externalInsertionMixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt
      externalTime σ x y

variable {E₁ E₂ m n : ℕ}

/-- Transport a timed event along increasing reindexings of its external and interaction slots. -/
def externalInsertionTimedEventMap
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n) :
    ExternalInsertionTimedEvent E₁ m → ExternalInsertionTimedEvent E₂ n :=
  Sum.map fExternal fInteraction

theorem externalInsertionTimedEventMap_injective
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : Function.Injective fExternal)
    (hInteraction : Function.Injective fInteraction) :
    Function.Injective (externalInsertionTimedEventMap fExternal fInteraction) := by
  simpa [externalInsertionTimedEventMap] using
    (Sum.map_injective.mpr ⟨hExternal, hInteraction⟩)

@[simp]
theorem externalInsertionTimedEventTime_map
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (event : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventTime externalTime σ
        (externalInsertionTimedEventMap fExternal fInteraction event) =
      externalInsertionTimedEventTime (externalTime ∘ fExternal) (σ ∘ fInteraction) event := by
  cases event <;> rfl

theorem externalInsertionTimedEventRank_map_le_iff
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventRank
        (externalInsertionTimedEventMap fExternal fInteraction a) ≤
      externalInsertionTimedEventRank
        (externalInsertionTimedEventMap fExternal fInteraction b) ↔
    externalInsertionTimedEventRank a ≤ externalInsertionTimedEventRank b := by
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          simpa [externalInsertionTimedEventMap, externalInsertionTimedEventRank] using
            hExternal.le_iff_le
      | inr b =>
          have ha := a.isLt
          have hfa := (fExternal a).isLt
          simp [externalInsertionTimedEventMap, externalInsertionTimedEventRank]
          omega
  | inr a =>
      cases b with
      | inl b =>
          have hb := b.isLt
          have hfb := (fExternal b).isLt
          simp [externalInsertionTimedEventMap, externalInsertionTimedEventRank]
          omega
      | inr b =>
          have h := hInteraction.le_iff_le
          simp [externalInsertionTimedEventMap, externalInsertionTimedEventRank] at h ⊢
          omega

theorem externalInsertionTimedEventBeforeOrEqual_map_iff
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventBeforeOrEqual externalTime σ
        (externalInsertionTimedEventMap fExternal fInteraction a)
        (externalInsertionTimedEventMap fExternal fInteraction b) ↔
      externalInsertionTimedEventBeforeOrEqual
        (externalTime ∘ fExternal) (σ ∘ fInteraction) a b := by
  simp only [externalInsertionTimedEventBeforeOrEqual, externalInsertionTimedEventTime_map]
  rw [externalInsertionTimedEventRank_map_le_iff hExternal hInteraction]

theorem externalInsertionTimedEventBefore_map_iff
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventBefore externalTime σ
        (externalInsertionTimedEventMap fExternal fInteraction a)
        (externalInsertionTimedEventMap fExternal fInteraction b) ↔
      externalInsertionTimedEventBefore
        (externalTime ∘ fExternal) (σ ∘ fInteraction) a b := by
  simp only [externalInsertionTimedEventBefore]
  rw [externalInsertionTimedEventBeforeOrEqual_map_iff hExternal hInteraction]
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab => hne
      (congrArg (externalInsertionTimedEventMap fExternal fInteraction) hab)⟩
  · rintro ⟨h, hne⟩
    exact ⟨h, fun hab => hne
      (externalInsertionTimedEventMap_injective
        hExternal.injective hInteraction.injective hab)⟩

theorem orderedExternalInsertionTimedEventPosition_map_lt_iff
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E₁ m) :
    orderedExternalInsertionTimedEventPosition externalTime σ
        (externalInsertionTimedEventMap fExternal fInteraction a) <
      orderedExternalInsertionTimedEventPosition externalTime σ
        (externalInsertionTimedEventMap fExternal fInteraction b) ↔
    orderedExternalInsertionTimedEventPosition
        (externalTime ∘ fExternal) (σ ∘ fInteraction) a <
      orderedExternalInsertionTimedEventPosition
        (externalTime ∘ fExternal) (σ ∘ fInteraction) b := by
  rw [orderedExternalInsertionTimedEventPosition_lt_iff,
    orderedExternalInsertionTimedEventPosition_lt_iff,
    externalInsertionTimedEventBefore_map_iff hExternal hInteraction]

/-- Transport a canonical leg along increasing reindexings of external and interaction slots. -/
def orderedExternalInsertionLegMap
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n) :
    OrderedExternalInsertionLeg E₁ m → OrderedExternalInsertionLeg E₂ n
  | .inl e => .inl (fExternal e)
  | .inr p => .inr (⟨fInteraction p.1.1, Finset.mem_univ _⟩, p.2)

theorem orderedExternalInsertionLegMap_injective
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : Function.Injective fExternal)
    (hInteraction : Function.Injective fInteraction) :
    Function.Injective (orderedExternalInsertionLegMap fExternal fInteraction) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl (hExternal (Sum.inl.inj h))
      | inr y => cases h
  | inr x =>
      cases y with
      | inl y => cases h
      | inr y =>
          apply congrArg Sum.inr
          apply Prod.ext
          · apply Subtype.ext
            exact hInteraction (congrArg (fun z => z.1.1) (Sum.inr.inj h))
          · exact congrArg (fun z => z.2) (Sum.inr.inj h)

@[simp]
theorem orderedExternalInsertionLegEvent_map
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n)
    (leg : OrderedExternalInsertionLeg E₁ m) :
    orderedExternalInsertionLegEvent
        (orderedExternalInsertionLegMap fExternal fInteraction leg) =
      externalInsertionTimedEventMap fExternal fInteraction
        (orderedExternalInsertionLegEvent leg) := by
  cases leg <;> rfl

theorem externalInsertionTimedEventAtomicLegs_map
    (fExternal : Fin (2 * E₁) → Fin (2 * E₂))
    (fInteraction : Fin m → Fin n)
    (event : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventAtomicLegs
        (externalInsertionTimedEventMap fExternal fInteraction event) =
      (externalInsertionTimedEventAtomicLegs event).map
        (orderedExternalInsertionLegMap fExternal fInteraction) := by
  cases event with
  | inl e => simp [externalInsertionTimedEventMap, externalInsertionTimedEventAtomicLegs,
      orderedExternalInsertionLegMap]
  | inr v => simp [externalInsertionTimedEventMap, externalInsertionTimedEventAtomicLegs,
      orderedExternalInsertionLegMap]

/-- The ambient mixed atomic order restricts to the mixed atomic order of increasing external and
interaction slot families. -/
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_map_lt_iff
    {fExternal : Fin (2 * E₁) → Fin (2 * E₂)}
    {fInteraction : Fin m → Fin n}
    (hExternal : StrictMono fExternal) (hInteraction : StrictMono fInteraction)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E₁ m) :
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap fExternal fInteraction x) <
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap fExternal fInteraction y) ↔
    externalInsertionMixedTimeOrderedAtomicLegPosition
        (externalTime ∘ fExternal) (σ ∘ fInteraction) x <
      externalInsertionMixedTimeOrderedAtomicLegPosition
        (externalTime ∘ fExternal) (σ ∘ fInteraction) y := by
  classical
  letI : BEq (OrderedExternalInsertionLeg E₁ m) := instBEqOfDecidableEq
  letI : BEq (OrderedExternalInsertionLeg E₂ n) := instBEqOfDecidableEq
  have hInj := orderedExternalInsertionLegMap_injective
    hExternal.injective hInteraction.injective
  by_cases hxy : orderedExternalInsertionLegEvent x = orderedExternalInsertionLegEvent y
  · let event := orderedExternalInsertionLegEvent x
    have hx : x ∈ externalInsertionTimedEventAtomicLegs event := by
      simpa [event] using orderedExternalInsertionLeg_mem_eventAtomicLegs x
    have hy : y ∈ externalInsertionTimedEventAtomicLegs event := by
      simpa [event, hxy] using orderedExternalInsertionLeg_mem_eventAtomicLegs y
    have hxMap : orderedExternalInsertionLegMap fExternal fInteraction x ∈
        externalInsertionTimedEventAtomicLegs
          (externalInsertionTimedEventMap fExternal fInteraction event) := by
      rw [externalInsertionTimedEventAtomicLegs_map]
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    have hyMap : orderedExternalInsertionLegMap fExternal fInteraction y ∈
        externalInsertionTimedEventAtomicLegs
          (externalInsertionTimedEventMap fExternal fInteraction event) := by
      rw [externalInsertionTimedEventAtomicLegs_map]
      exact List.mem_map.2 ⟨y, hy, rfl⟩
    have hLocal := List.idxOf_flatMap_block_lt_iff externalInsertionTimedEventAtomicLegs
      (orderedExternalInsertionTimedEvents
        (externalTime ∘ fExternal) (σ ∘ fInteraction))
      event x y
      (externalInsertionMixedTimeOrderedAtomicLegs_nodup
        (externalTime ∘ fExternal) (σ ∘ fInteraction))
      (orderedExternalInsertionTimedEvents_all_mem
        (externalTime ∘ fExternal) (σ ∘ fInteraction) event) hx hy
    have hAmbient := List.idxOf_flatMap_block_lt_iff externalInsertionTimedEventAtomicLegs
      (orderedExternalInsertionTimedEvents externalTime σ)
      (externalInsertionTimedEventMap fExternal fInteraction event)
      (orderedExternalInsertionLegMap fExternal fInteraction x)
      (orderedExternalInsertionLegMap fExternal fInteraction y)
      (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
      (orderedExternalInsertionTimedEvents_all_mem externalTime σ
        (externalInsertionTimedEventMap fExternal fInteraction event)) hxMap hyMap
    have hidx (z : OrderedExternalInsertionLeg E₁ m) :
        ((externalInsertionTimedEventAtomicLegs event).map
          (orderedExternalInsertionLegMap fExternal fInteraction)).idxOf
            (orderedExternalInsertionLegMap fExternal fInteraction z) =
          (externalInsertionTimedEventAtomicLegs event).idxOf z := by
      unfold List.idxOf
      rw [List.findIdx_map]
      apply congrArg (fun p => (externalInsertionTimedEventAtomicLegs event).findIdx p)
      funext w
      simp [hInj.eq_iff]
    calc
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap fExternal fInteraction x) <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap fExternal fInteraction y) ↔
        (externalInsertionTimedEventAtomicLegs
          (externalInsertionTimedEventMap fExternal fInteraction event)).idxOf
            (orderedExternalInsertionLegMap fExternal fInteraction x) <
          (externalInsertionTimedEventAtomicLegs
            (externalInsertionTimedEventMap fExternal fInteraction event)).idxOf
              (orderedExternalInsertionLegMap fExternal fInteraction y) := by
          simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
            externalInsertionMixedTimeOrderedAtomicLegs] using hAmbient
      _ ↔ (externalInsertionTimedEventAtomicLegs event).idxOf x <
          (externalInsertionTimedEventAtomicLegs event).idxOf y := by
            rw [externalInsertionTimedEventAtomicLegs_map, hidx x, hidx y]
      _ ↔ externalInsertionMixedTimeOrderedAtomicLegPosition
            (externalTime ∘ fExternal) (σ ∘ fInteraction) x <
          externalInsertionMixedTimeOrderedAtomicLegPosition
            (externalTime ∘ fExternal) (σ ∘ fInteraction) y := by
            symm
            simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
              externalInsertionMixedTimeOrderedAtomicLegs] using hLocal
  · have hxyMap :
      orderedExternalInsertionLegEvent
          (orderedExternalInsertionLegMap fExternal fInteraction x) ≠
        orderedExternalInsertionLegEvent
          (orderedExternalInsertionLegMap fExternal fInteraction y) := by
      rw [orderedExternalInsertionLegEvent_map, orderedExternalInsertionLegEvent_map]
      exact fun hEq => hxy
        (externalInsertionTimedEventMap_injective
          hExternal.injective hInteraction.injective hEq)
    rw [externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
        externalTime σ _ _ hxyMap,
      externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
        (externalTime ∘ fExternal) (σ ∘ fInteraction) x y hxy,
      orderedExternalInsertionLegEvent_map, orderedExternalInsertionLegEvent_map,
      orderedExternalInsertionTimedEventPosition_map_lt_iff
        hExternal hInteraction externalTime σ]

/-- Permutation from the fixed flattened diagram-leg order to mixed-time atomic positions. -/
noncomputable def externalInsertionStandardToMixedAtomicPositionEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (finCongr (by simp)).trans
    ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).trans
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm)

end Common
end SecondQuantization
