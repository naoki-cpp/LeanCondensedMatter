import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Mixed-time order for arbitrary external insertions

This module provides only the ordering data needed by the higher-point fermionic consumer:

* sort the `2 * E` external events together with `n` interaction events by imaginary time;
* expand that event order to the corresponding atomic legs;
* identify the time-ordered atomic positions with the fixed flattened
  `ExternalInsertionDiagram` positions.

Further transport and locality lemmas are intentionally deferred until a concrete amplitude
factorization proof needs them.
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

private def externalInsertionTimedEventRank {E n : ℕ}
    (event : ExternalInsertionTimedEvent E n) : ℕ :=
  ((finSumFinEquiv : ExternalInsertionTimedEvent E n ≃ Fin (2 * E + n)) event).val

private def externalInsertionTimedEventBeforeOrEqual {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (a b : ExternalInsertionTimedEvent E n) : Prop :=
  externalInsertionTimedEventTime externalTime σ b <
      externalInsertionTimedEventTime externalTime σ a ∨
    (externalInsertionTimedEventTime externalTime σ a =
        externalInsertionTimedEventTime externalTime σ b ∧
      externalInsertionTimedEventRank a ≤ externalInsertionTimedEventRank b)

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

private theorem orderedExternalInsertionTimedEvents_perm {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List.Perm (orderedExternalInsertionTimedEvents externalTime σ)
      (canonicalExternalInsertionTimedEvents E n) := by
  classical
  exact List.perm_insertionSort _ _

private theorem orderedExternalInsertionTimedEvents_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (orderedExternalInsertionTimedEvents externalTime σ).Nodup :=
  (orderedExternalInsertionTimedEvents_perm externalTime σ).nodup_iff.mpr
    (canonicalExternalInsertionTimedEvents_nodup E n)

private theorem orderedExternalInsertionTimedEvents_all_mem {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ∀ event : ExternalInsertionTimedEvent E n,
      event ∈ orderedExternalInsertionTimedEvents externalTime σ := by
  intro event
  exact (orderedExternalInsertionTimedEvents_perm externalTime σ).symm.subset
    (canonicalExternalInsertionTimedEvents_all_mem E n event)

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

/-- Permutation from the fixed flattened diagram-leg order to mixed-time atomic positions. -/
noncomputable def externalInsertionStandardToMixedAtomicPositionEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (finCongr (by simp)).trans
    ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).trans
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm)

end Common
end SecondQuantization
