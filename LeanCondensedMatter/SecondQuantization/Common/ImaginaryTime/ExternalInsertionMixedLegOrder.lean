import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.Combinatorics.ListFlatMapOrder
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Statistics-independent mixed leg order for external insertions

The mixed event order for `2 * E` external insertions induces an atomic-leg order: every external
event contributes one leg and every quartic interaction event contributes its four local legs in
their fixed order. This module gives the resulting exact enumeration and transports its relative
order along strictly monotone reindexings of both external and interaction slots.

No operator realization, contraction kernel, Gibbs state, or fermionic sign appears here.
-/

namespace SecondQuantization
namespace Common

/-- The standard external-insertion leg type with `n` ordered interaction slots. -/
abbrev OrderedExternalInsertionLeg (E n : ℕ) : Type :=
  ExternalInsertionLeg E (Finset.univ : Finset (Fin n))

/-- Atomic leg identities contributed by one mixed event. -/
def externalInsertionTimedEventAtomicLegs {E n : ℕ} :
    ExternalInsertionTimedEvent E n → List (OrderedExternalInsertionLeg E n)
  | .inl e => [Sum.inl e]
  | .inr v => List.ofFn fun l : Fin 4 =>
      Sum.inr (⟨v, Finset.mem_univ v⟩, l)

@[simp]
theorem externalInsertionTimedEventAtomicLegs_external {E n : ℕ}
    (e : Fin (2 * E)) :
    externalInsertionTimedEventAtomicLegs (n := n) (Sum.inl e) = [Sum.inl e] :=
  rfl

@[simp]
theorem externalInsertionTimedEventAtomicLegs_interaction {E n : ℕ}
    (v : Fin n) :
    externalInsertionTimedEventAtomicLegs (E := E) (Sum.inr v) =
      List.ofFn (fun l : Fin 4 =>
        Sum.inr (⟨v, Finset.mem_univ v⟩, l)) :=
  rfl

/-- The canonical event enumeration expanded to atomic leg identities. -/
def canonicalExternalInsertionAtomicLegs (E n : ℕ) :
    List (OrderedExternalInsertionLeg E n) :=
  (canonicalExternalInsertionTimedEvents E n).flatMap
    externalInsertionTimedEventAtomicLegs

/-- Atomic leg identities parallel to the mixed-time event order. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegs {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List (OrderedExternalInsertionLeg E n) :=
  (orderedExternalInsertionTimedEvents externalTime σ).flatMap
    externalInsertionTimedEventAtomicLegs

/-- Mixed time ordering only permutes the complete canonical atomic-leg list. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_perm_canonical {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    List.Perm (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ)
      (canonicalExternalInsertionAtomicLegs E n) := by
  simpa [externalInsertionMixedTimeOrderedAtomicLegs,
    canonicalExternalInsertionAtomicLegs] using
    (orderedExternalInsertionTimedEvents_perm externalTime σ).flatMap
      (fun event _ =>
        List.Perm.refl (externalInsertionTimedEventAtomicLegs event))

private theorem externalInsertionTimedEventAtomicLegs_nodup {E n : ℕ}
    (event : ExternalInsertionTimedEvent E n) :
    (externalInsertionTimedEventAtomicLegs event).Nodup := by
  cases event with
  | inl e => simp
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
      | inl e' => simpa using h.symm
      | inr v => simp
  | inr v =>
      cases b with
      | inl e => simp
      | inr v' =>
          have hv : v ≠ v' := by
            intro hv
            apply h
            cases hv
            rfl
          simpa using hv.symm

/-- The mixed-time atomic-leg list has no duplicate identities. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_nodup {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).Nodup := by
  rw [externalInsertionMixedTimeOrderedAtomicLegs, List.nodup_flatMap]
  refine ⟨
    fun event _ => externalInsertionTimedEventAtomicLegs_nodup event,
    ?_⟩
  exact
    (orderedExternalInsertionTimedEvents_nodup externalTime σ).pairwise_of_forall_ne
      (fun _ _ _ _ h => externalInsertionTimedEventAtomicLegs_disjoint h)

/-- Every canonical external or interaction leg occurs in the mixed-time atomic-leg list. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_all_mem {E n : ℕ}
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
        by simp⟩
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      refine ⟨
        Sum.inr v,
        orderedExternalInsertionTimedEvents_all_mem externalTime σ (Sum.inr v),
        ?_⟩
      rw [externalInsertionTimedEventAtomicLegs_interaction, List.mem_ofFn]
      exact ⟨l, rfl⟩

/-- The mixed-time atomic-leg list has `2 * E + 4 * n` entries. -/
theorem externalInsertionMixedTimeOrderedAtomicLegs_length {E n : ℕ}
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

/-- Ambient permutation from the canonical flattened diagram-leg order to mixed-time positions. -/
noncomputable def externalInsertionStandardToMixedAtomicPositionEquiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (finCongr (by simp)).trans
    ((externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).trans
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm)

/-- The mixed event supporting one canonical external-insertion leg. -/
def orderedExternalInsertionLegEvent {E n : ℕ} :
    OrderedExternalInsertionLeg E n → ExternalInsertionTimedEvent E n
  | .inl e => .inl e
  | .inr p => .inr p.1.1

/-- Every canonical leg belongs to the local atomic-leg list of its supporting event. -/
theorem orderedExternalInsertionLeg_mem_eventAtomicLegs {E n : ℕ}
    (leg : OrderedExternalInsertionLeg E n) :
    leg ∈ externalInsertionTimedEventAtomicLegs
      (orderedExternalInsertionLegEvent leg) := by
  cases leg with
  | inl e => simp [orderedExternalInsertionLegEvent]
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      rw [orderedExternalInsertionLegEvent,
        externalInsertionTimedEventAtomicLegs_interaction, List.mem_ofFn]
      exact ⟨l, rfl⟩

/-- Mixed-time position occupied by one canonical external-insertion leg identity. -/
noncomputable def externalInsertionMixedTimeOrderedAtomicLegPosition {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    Fin (2 * (2 * n + E)) := by
  classical
  letI : BEq (OrderedExternalInsertionLeg E n) := instBEqOfDecidableEq
  refine ⟨
    (externalInsertionMixedTimeOrderedAtomicLegs externalTime σ).idxOf leg,
    ?_⟩
  rw [← externalInsertionMixedTimeOrderedAtomicLegs_length externalTime σ]
  exact List.idxOf_lt_length_iff.mpr
    (externalInsertionMixedTimeOrderedAtomicLegs_all_mem externalTime σ leg)

/-- Selecting the position of the leg read at a mixed-time position is identity. -/
@[simp]
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_equiv {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + E))) :
    externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ p) = p := by
  exact
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).symm_apply_apply p

/-- Reading the leg at the mixed-time position selected by that leg is identity. -/
@[simp]
theorem externalInsertionMixedTimeOrderedAtomicLegEquiv_position {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (leg : OrderedExternalInsertionLeg E n) :
    externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ leg) = leg := by
  exact
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ).apply_symm_apply leg

/-- Legs in one mixed-time event block have identical comparison with every leg outside that block. -/
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_lt_uniform
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (event : ExternalInsertionTimedEvent E n)
    (x y z : OrderedExternalInsertionLeg E n)
    (hEvent : event ∈ orderedExternalInsertionTimedEvents externalTime σ)
    (hx : x ∈ externalInsertionTimedEventAtomicLegs event)
    (hy : y ∈ externalInsertionTimedEventAtomicLegs event)
    (hz : z ∈ externalInsertionMixedTimeOrderedAtomicLegs externalTime σ)
    (hzOutside : z ∉ externalInsertionTimedEventAtomicLegs event) :
    (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ x <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ z) =
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ y <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ z) := by
  classical
  letI : BEq (OrderedExternalInsertionLeg E n) := instBEqOfDecidableEq
  have h :=
    List.idxOf_flatMap_block_lt_uniform externalInsertionTimedEventAtomicLegs
      (orderedExternalInsertionTimedEvents externalTime σ) event x y z
      (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
      hEvent hx hy hz hzOutside
  simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
    externalInsertionMixedTimeOrderedAtomicLegs] using h

private theorem
    externalInsertionMixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E n)
    (hEvent :
      orderedExternalInsertionTimedEventPosition externalTime σ
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
  have h :=
    List.idxOf_flatMap_lt_of_idxOf_lt externalInsertionTimedEventAtomicLegs
      (orderedExternalInsertionTimedEvents externalTime σ)
      (orderedExternalInsertionLegEvent x)
      (orderedExternalInsertionLegEvent y) x y
      (orderedExternalInsertionTimedEvents_nodup externalTime σ)
      (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
      (orderedExternalInsertionTimedEvents_all_mem externalTime σ
        (orderedExternalInsertionLegEvent x))
      (orderedExternalInsertionTimedEvents_all_mem externalTime σ
        (orderedExternalInsertionLegEvent y))
      (orderedExternalInsertionLeg_mem_eventAtomicLegs x)
      (orderedExternalInsertionLeg_mem_eventAtomicLegs y)
      hEventIdx
  simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
    externalInsertionMixedTimeOrderedAtomicLegs] using h

/-- For legs supported on distinct events, mixed atomic-leg order is exactly mixed event order. -/
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E n)
    (hxy :
      orderedExternalInsertionLegEvent x ≠ orderedExternalInsertionLegEvent y) :
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
    · exact
        (hxy
          ((orderedExternalInsertionTimedEventEquiv externalTime σ).symm.injective
            hEvent)).elim
    · have hReverse :=
        externalInsertionMixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt
          externalTime σ y x hEvent
      exact (lt_asymm hLeg hReverse).elim
  · exact
      externalInsertionMixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt
        externalTime σ x y

/-- Relative atomic-leg positions are unchanged when the supporting event-time comparison is
unchanged. -/
theorem
    externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E n)
    (hEvent :
      (orderedExternalInsertionTimedEventPosition externalTime σ
          (orderedExternalInsertionLegEvent x) <
        orderedExternalInsertionTimedEventPosition externalTime σ
          (orderedExternalInsertionLegEvent y)) ↔
      (orderedExternalInsertionTimedEventPosition externalTime υ
          (orderedExternalInsertionLegEvent x) <
        orderedExternalInsertionTimedEventPosition externalTime υ
          (orderedExternalInsertionLegEvent y))) :
    (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ x <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ y) ↔
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime υ x <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime υ y) := by
  classical
  letI : BEq (OrderedExternalInsertionLeg E n) := instBEqOfDecidableEq
  by_cases hxy :
      orderedExternalInsertionLegEvent x = orderedExternalInsertionLegEvent y
  · let event := orderedExternalInsertionLegEvent x
    have hx : x ∈ externalInsertionTimedEventAtomicLegs event := by
      simpa [event] using orderedExternalInsertionLeg_mem_eventAtomicLegs x
    have hy : y ∈ externalInsertionTimedEventAtomicLegs event := by
      simpa [event, hxy] using orderedExternalInsertionLeg_mem_eventAtomicLegs y
    have hσ :=
      List.idxOf_flatMap_block_lt_iff externalInsertionTimedEventAtomicLegs
        (orderedExternalInsertionTimedEvents externalTime σ) event x y
        (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
        (orderedExternalInsertionTimedEvents_all_mem externalTime σ event)
        hx hy
    have hυ :=
      List.idxOf_flatMap_block_lt_iff externalInsertionTimedEventAtomicLegs
        (orderedExternalInsertionTimedEvents externalTime υ) event x y
        (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime υ)
        (orderedExternalInsertionTimedEvents_all_mem externalTime υ event)
        hx hy
    calc
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ x <
          externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ y ↔
        (externalInsertionTimedEventAtomicLegs event).idxOf x <
          (externalInsertionTimedEventAtomicLegs event).idxOf y := by
            simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
              externalInsertionMixedTimeOrderedAtomicLegs] using hσ
      _ ↔
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime υ x <
          externalInsertionMixedTimeOrderedAtomicLegPosition externalTime υ y := by
            symm
            simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
              externalInsertionMixedTimeOrderedAtomicLegs] using hυ
  · rw [
      externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
        externalTime σ x y hxy,
      externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
        externalTime υ x y hxy]
    exact hEvent

/-- Relative atomic-leg positions depend only on the physical times of their supporting events and
their fixed local coordinates. -/
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_of_eventTime_eq
    {E n : ℕ} (externalTime : Fin (2 * E) → ℝ) (σ υ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E n)
    (hxTime :
      externalInsertionTimedEventTime externalTime σ
          (orderedExternalInsertionLegEvent x) =
        externalInsertionTimedEventTime externalTime υ
          (orderedExternalInsertionLegEvent x))
    (hyTime :
      externalInsertionTimedEventTime externalTime σ
          (orderedExternalInsertionLegEvent y) =
        externalInsertionTimedEventTime externalTime υ
          (orderedExternalInsertionLegEvent y)) :
    (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ x <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ y) ↔
      (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime υ x <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime υ y) :=
  externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff
    externalTime σ υ x y
    (orderedExternalInsertionTimedEventPosition_lt_iff_of_eventTime_eq
      externalTime σ υ
      (orderedExternalInsertionLegEvent x)
      (orderedExternalInsertionLegEvent y)
      hxTime hyTime)

variable {E₁ E₂ m n : ℕ}

/-- Transport a canonical atomic leg along external- and interaction-slot reindexings. -/
def orderedExternalInsertionLegMap
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n) :
    OrderedExternalInsertionLeg E₁ m → OrderedExternalInsertionLeg E₂ n :=
  Sum.map externalMap <|
    Prod.map
      (fun v => ⟨interactionMap (v : Fin m), Finset.mem_univ _⟩) id

@[simp]
theorem orderedExternalInsertionLegMap_inl
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n) (e : Fin (2 * E₁)) :
    orderedExternalInsertionLegMap externalMap interactionMap (Sum.inl e) =
      Sum.inl (externalMap e) :=
  rfl

@[simp]
theorem orderedExternalInsertionLegMap_inr
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n)
    (v : ↥(Finset.univ : Finset (Fin m))) (l : Fin 4) :
    orderedExternalInsertionLegMap externalMap interactionMap (Sum.inr (v, l)) =
      Sum.inr
        (⟨interactionMap (v : Fin m), Finset.mem_univ _⟩, l) :=
  rfl

/-- Injective slot maps transport distinct atomic legs to distinct atomic legs. -/
theorem orderedExternalInsertionLegMap_injective
    {externalMap : Fin (2 * E₁) → Fin (2 * E₂)}
    {interactionMap : Fin m → Fin n}
    (hExternal : Function.Injective externalMap)
    (hInteraction : Function.Injective interactionMap) :
    Function.Injective
      (orderedExternalInsertionLegMap externalMap interactionMap) := by
  unfold orderedExternalInsertionLegMap
  apply Function.Injective.sumMap
  · exact hExternal
  · apply Function.Injective.prodMap
    · intro v w h
      exact Subtype.ext (hInteraction (congrArg Subtype.val h))
    · exact Function.injective_id

/-- A transported atomic leg is supported on the transported event. -/
@[simp]
theorem orderedExternalInsertionLegEvent_map
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n)
    (leg : OrderedExternalInsertionLeg E₁ m) :
    orderedExternalInsertionLegEvent
        (orderedExternalInsertionLegMap externalMap interactionMap leg) =
      externalInsertionTimedEventMap externalMap interactionMap
        (orderedExternalInsertionLegEvent leg) := by
  cases leg with
  | inl e => rfl
  | inr p => rfl

/-- The atomic-leg list of an event is relabeled, not reordered. -/
theorem externalInsertionTimedEventAtomicLegs_map
    (externalMap : Fin (2 * E₁) → Fin (2 * E₂))
    (interactionMap : Fin m → Fin n)
    (event : ExternalInsertionTimedEvent E₁ m) :
    externalInsertionTimedEventAtomicLegs
        (externalInsertionTimedEventMap externalMap interactionMap event) =
      (externalInsertionTimedEventAtomicLegs event).map
        (orderedExternalInsertionLegMap externalMap interactionMap) := by
  cases event with
  | inl e => simp
  | inr v => simp

/-- The ambient mixed atomic-leg order restricts exactly to the mixed order on strictly monotone
external and interaction subfamilies. -/
theorem externalInsertionMixedTimeOrderedAtomicLegPosition_map_lt_iff
    {externalMap : Fin (2 * E₁) → Fin (2 * E₂)}
    {interactionMap : Fin m → Fin n}
    (hExternal : StrictMono externalMap)
    (hInteraction : StrictMono interactionMap)
    (externalTime : Fin (2 * E₂) → ℝ) (σ : Fin n → ℝ)
    (x y : OrderedExternalInsertionLeg E₁ m) :
    (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap externalMap interactionMap x) <
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap externalMap interactionMap y)) ↔
    (externalInsertionMixedTimeOrderedAtomicLegPosition
        (externalTime ∘ externalMap) (σ ∘ interactionMap) x <
      externalInsertionMixedTimeOrderedAtomicLegPosition
        (externalTime ∘ externalMap) (σ ∘ interactionMap) y) := by
  classical
  letI : BEq (OrderedExternalInsertionLeg E₁ m) := instBEqOfDecidableEq
  letI : BEq (OrderedExternalInsertionLeg E₂ n) := instBEqOfDecidableEq
  have hInj :=
    orderedExternalInsertionLegMap_injective
      hExternal.injective hInteraction.injective
  by_cases hxy :
      orderedExternalInsertionLegEvent x = orderedExternalInsertionLegEvent y
  · let event := orderedExternalInsertionLegEvent x
    have hx : x ∈ externalInsertionTimedEventAtomicLegs event := by
      simpa [event] using orderedExternalInsertionLeg_mem_eventAtomicLegs x
    have hy : y ∈ externalInsertionTimedEventAtomicLegs event := by
      simpa [event, hxy] using orderedExternalInsertionLeg_mem_eventAtomicLegs y
    have hxMap :
        orderedExternalInsertionLegMap externalMap interactionMap x ∈
          externalInsertionTimedEventAtomicLegs
            (externalInsertionTimedEventMap externalMap interactionMap event) := by
      rw [externalInsertionTimedEventAtomicLegs_map]
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    have hyMap :
        orderedExternalInsertionLegMap externalMap interactionMap y ∈
          externalInsertionTimedEventAtomicLegs
            (externalInsertionTimedEventMap externalMap interactionMap event) := by
      rw [externalInsertionTimedEventAtomicLegs_map]
      exact List.mem_map.2 ⟨y, hy, rfl⟩
    have hPiece :=
      List.idxOf_flatMap_block_lt_iff externalInsertionTimedEventAtomicLegs
        (orderedExternalInsertionTimedEvents
          (externalTime ∘ externalMap) (σ ∘ interactionMap))
        event x y
        (externalInsertionMixedTimeOrderedAtomicLegs_nodup
          (externalTime ∘ externalMap) (σ ∘ interactionMap))
        (orderedExternalInsertionTimedEvents_all_mem
          (externalTime ∘ externalMap) (σ ∘ interactionMap) event)
        hx hy
    have hAmbient :=
      List.idxOf_flatMap_block_lt_iff externalInsertionTimedEventAtomicLegs
        (orderedExternalInsertionTimedEvents externalTime σ)
        (externalInsertionTimedEventMap externalMap interactionMap event)
        (orderedExternalInsertionLegMap externalMap interactionMap x)
        (orderedExternalInsertionLegMap externalMap interactionMap y)
        (externalInsertionMixedTimeOrderedAtomicLegs_nodup externalTime σ)
        (orderedExternalInsertionTimedEvents_all_mem externalTime σ
          (externalInsertionTimedEventMap externalMap interactionMap event))
        hxMap hyMap
    have hidx (z : OrderedExternalInsertionLeg E₁ m) :
        ((externalInsertionTimedEventAtomicLegs event).map
          (orderedExternalInsertionLegMap externalMap interactionMap)).idxOf
            (orderedExternalInsertionLegMap externalMap interactionMap z) =
          (externalInsertionTimedEventAtomicLegs event).idxOf z := by
      unfold List.idxOf
      rw [List.findIdx_map]
      apply congrArg
        (fun p => (externalInsertionTimedEventAtomicLegs event).findIdx p)
      funext w
      simp [hInj.eq_iff]
    calc
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap externalMap interactionMap x) <
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap externalMap interactionMap y) ↔
        (externalInsertionTimedEventAtomicLegs
          (externalInsertionTimedEventMap externalMap interactionMap event)).idxOf
            (orderedExternalInsertionLegMap externalMap interactionMap x) <
          (externalInsertionTimedEventAtomicLegs
            (externalInsertionTimedEventMap externalMap interactionMap event)).idxOf
              (orderedExternalInsertionLegMap externalMap interactionMap y) := by
            simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
              externalInsertionMixedTimeOrderedAtomicLegs] using hAmbient
      _ ↔
        (externalInsertionTimedEventAtomicLegs event).idxOf x <
          (externalInsertionTimedEventAtomicLegs event).idxOf y := by
            rw [externalInsertionTimedEventAtomicLegs_map, hidx x, hidx y]
      _ ↔
        externalInsertionMixedTimeOrderedAtomicLegPosition
            (externalTime ∘ externalMap) (σ ∘ interactionMap) x <
          externalInsertionMixedTimeOrderedAtomicLegPosition
            (externalTime ∘ externalMap) (σ ∘ interactionMap) y := by
            symm
            simpa [externalInsertionMixedTimeOrderedAtomicLegPosition,
              externalInsertionMixedTimeOrderedAtomicLegs] using hPiece
  · have hxyMap :
      orderedExternalInsertionLegEvent
          (orderedExternalInsertionLegMap externalMap interactionMap x) ≠
        orderedExternalInsertionLegEvent
          (orderedExternalInsertionLegMap externalMap interactionMap y) := by
      rw [orderedExternalInsertionLegEvent_map,
        orderedExternalInsertionLegEvent_map]
      exact fun hEq =>
        hxy
          (externalInsertionTimedEventMap_injective
            hExternal.injective hInteraction.injective hEq)
    rw [
      externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
        externalTime σ _ _ hxyMap,
      externalInsertionMixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
        (externalTime ∘ externalMap) (σ ∘ interactionMap) x y hxy,
      orderedExternalInsertionLegEvent_map,
      orderedExternalInsertionLegEvent_map,
      orderedExternalInsertionTimedEventPosition_map_lt_iff
        hExternal hInteraction]

end Common
end SecondQuantization
