import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedEventSlotEmbedding
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram
import LeanCondensedMatter.Combinatorics.ListFlatMapOrder
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Statistics-independent mixed two-point leg order

The mixed two-point event order is statistics-independent, and so is the induced order on the two
external legs and the four local legs of every interaction event. This module owns the standard leg
identities, the mixed-time leg enumeration, event-block order lemmas, and monotone interaction-slot
transport.

No operator realization, Gibbs state, contraction kernel, or exchange sign appears here.
-/

namespace SecondQuantization
namespace Common

/-- The standard two-point leg type for `n` interaction slots. -/
abbrev OrderedTwoPointLeg (n : ℕ) : Type :=
  TwoPointLeg (Finset.univ : Finset (Fin n))

/-- The standard two-point vertex type for `n` interaction slots. -/
abbrev OrderedTwoPointVertex (n : ℕ) : Type :=
  TwoPointVertex (Finset.univ : Finset (Fin n))

/-- The leg identities contributed by one external or interaction event. -/
def twoPointTimedEventAtomicLegs {n : ℕ} :
    TwoPointTimedEvent n → List (OrderedTwoPointLeg n)
  | .inl e => [Sum.inl e]
  | .inr v => List.ofFn fun l : Fin 4 =>
      Sum.inr (⟨v, Finset.mem_univ v⟩, l)

@[simp]
theorem twoPointTimedEventAtomicLegs_external {n : ℕ} (e : Fin 2) :
    twoPointTimedEventAtomicLegs (n := n) (Sum.inl e) = [Sum.inl e] :=
  rfl

@[simp]
theorem twoPointTimedEventAtomicLegs_interaction {n : ℕ} (v : Fin n) :
    twoPointTimedEventAtomicLegs (Sum.inr v) =
      List.ofFn (fun l : Fin 4 => Sum.inr (⟨v, Finset.mem_univ v⟩, l)) :=
  rfl

/-- The canonical event order expanded to standard two-point leg identities. -/
def canonicalTwoPointAtomicLegs (n : ℕ) : List (OrderedTwoPointLeg n) :=
  ([Sum.inl 0, Sum.inl 1] ++ twoPointInteractionEventList n).flatMap
    twoPointTimedEventAtomicLegs

/-- The leg identities parallel to the mixed-time event order. -/
noncomputable def mixedTimeOrderedAtomicLegs {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List (OrderedTwoPointLeg n) :=
  (orderedTwoPointTimedEvents τ τ' σ).flatMap twoPointTimedEventAtomicLegs

/-- Mixed time ordering only permutes the complete standard two-point leg list. -/
theorem mixedTimeOrderedAtomicLegs_perm_canonical {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    List.Perm (mixedTimeOrderedAtomicLegs τ τ' σ) (canonicalTwoPointAtomicLegs n) := by
  simpa [mixedTimeOrderedAtomicLegs, canonicalTwoPointAtomicLegs] using
    (orderedTwoPointTimedEvents_perm τ τ' σ).flatMap
      (fun event _ => List.Perm.refl (twoPointTimedEventAtomicLegs event))

private theorem twoPointTimedEventAtomicLegs_nodup {n : ℕ}
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicLegs event).Nodup := by
  cases event with
  | inl e => simp
  | inr v =>
      rw [twoPointTimedEventAtomicLegs]
      apply List.nodup_ofFn_ofInjective
      intro a b h
      exact congrArg Prod.snd (Sum.inr.inj h)

private theorem twoPointTimedEventAtomicLegs_disjoint {n : ℕ}
    {a b : TwoPointTimedEvent n} (h : a ≠ b) :
    List.Disjoint (twoPointTimedEventAtomicLegs a) (twoPointTimedEventAtomicLegs b) := by
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

/-- The mixed-time leg list has no duplicate leg identities. -/
theorem mixedTimeOrderedAtomicLegs_nodup {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicLegs τ τ' σ).Nodup := by
  rw [mixedTimeOrderedAtomicLegs, List.nodup_flatMap]
  refine ⟨fun event _ => twoPointTimedEventAtomicLegs_nodup event, ?_⟩
  exact (orderedTwoPointTimedEvents_nodup τ τ' σ).pairwise_of_forall_ne
    (fun _ _ _ _ h => twoPointTimedEventAtomicLegs_disjoint h)

/-- Every standard external or interaction leg occurs in the mixed-time leg list. -/
theorem mixedTimeOrderedAtomicLegs_all_mem {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    ∀ leg : OrderedTwoPointLeg n, leg ∈ mixedTimeOrderedAtomicLegs τ τ' σ := by
  intro leg
  rw [mixedTimeOrderedAtomicLegs, List.mem_flatMap]
  cases leg with
  | inl e =>
      exact ⟨Sum.inl e, orderedTwoPointTimedEvents_all_mem τ τ' σ (Sum.inl e), by simp⟩
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      refine ⟨Sum.inr v, orderedTwoPointTimedEvents_all_mem τ τ' σ (Sum.inr v), ?_⟩
      fin_cases l <;> simp [twoPointTimedEventAtomicLegs]

/-- The mixed-time leg list has exactly `4n + 2` entries. -/
theorem mixedTimeOrderedAtomicLegs_length {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicLegs τ τ' σ).length = 2 * (2 * n + 1) := by
  let l := mixedTimeOrderedAtomicLegs τ τ' σ
  have hcard : l.length = Fintype.card (OrderedTwoPointLeg n) := by
    simpa using Fintype.card_congr
      (List.Nodup.getEquivOfForallMemList l
        (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
        (mixedTimeOrderedAtomicLegs_all_mem τ τ' σ))
  rw [hcard]
  simp [OrderedTwoPointLeg]
  omega

/-- The exact bijection from mixed-time atomic positions to standard two-point legs. -/
noncomputable def mixedTimeOrderedAtomicLegEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) ≃ OrderedTwoPointLeg n :=
  (finCongr (mixedTimeOrderedAtomicLegs_length τ τ' σ).symm).trans
    (List.Nodup.getEquivOfForallMemList (mixedTimeOrderedAtomicLegs τ τ' σ)
      (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
      (mixedTimeOrderedAtomicLegs_all_mem τ τ' σ))

/-- The ambient permutation mapping a standard diagram-leg position to the corresponding
mixed-time atomic position. -/
noncomputable def standardToMixedAtomicPositionEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + 1))) :=
  (finCongr (by simp)).trans
    ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).trans
      (mixedTimeOrderedAtomicLegEquiv τ τ' σ).symm)

/-- The mixed event supporting one standard two-point leg. -/
def orderedTwoPointLegEvent {n : ℕ} : OrderedTwoPointLeg n → TwoPointTimedEvent n
  | .inl e => .inl e
  | .inr p => .inr p.1.1

/-- Every standard two-point leg belongs to the local leg list of its supporting event. -/
theorem orderedTwoPointLeg_mem_eventAtomicLegs {n : ℕ} (leg : OrderedTwoPointLeg n) :
    leg ∈ twoPointTimedEventAtomicLegs (orderedTwoPointLegEvent leg) := by
  cases leg with
  | inl e => simp [orderedTwoPointLegEvent]
  | inr p =>
      rcases p with ⟨⟨v, hv⟩, l⟩
      fin_cases l <;> simp [orderedTwoPointLegEvent, twoPointTimedEventAtomicLegs]

/-- The mixed position occupied by a standard two-point leg identity. -/
noncomputable def mixedTimeOrderedAtomicLegPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (leg : OrderedTwoPointLeg n) :
    Fin (2 * (2 * n + 1)) := by
  classical
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  refine ⟨(mixedTimeOrderedAtomicLegs τ τ' σ).idxOf leg, ?_⟩
  rw [← mixedTimeOrderedAtomicLegs_length τ τ' σ]
  exact List.idxOf_lt_length_iff.mpr (mixedTimeOrderedAtomicLegs_all_mem τ τ' σ leg)

/-- Legs in one mixed-time event block have identical comparison with every leg outside that block. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_uniform {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) (x y z : OrderedTwoPointLeg n)
    (hEvent : event ∈ orderedTwoPointTimedEvents τ τ' σ)
    (hx : x ∈ twoPointTimedEventAtomicLegs event)
    (hy : y ∈ twoPointTimedEventAtomicLegs event)
    (hz : z ∈ mixedTimeOrderedAtomicLegs τ τ' σ)
    (hzOutside : z ∉ twoPointTimedEventAtomicLegs event) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ z) =
      (mixedTimeOrderedAtomicLegPosition τ τ' σ y <
        mixedTimeOrderedAtomicLegPosition τ τ' σ z) := by
  classical
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  have h := List.idxOf_flatMap_block_lt_uniform twoPointTimedEventAtomicLegs
    (orderedTwoPointTimedEvents τ τ' σ) event x y z
    (mixedTimeOrderedAtomicLegs_nodup τ τ' σ) hEvent hx hy hz hzOutside
  simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegs] using h

private theorem mixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hEvent : orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x) <
      orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) :
    mixedTimeOrderedAtomicLegPosition τ τ' σ x <
      mixedTimeOrderedAtomicLegPosition τ τ' σ y := by
  classical
  letI : BEq (TwoPointTimedEvent n) := instBEqOfDecidableEq
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  have hEventIdx :
      (orderedTwoPointTimedEvents τ τ' σ).idxOf (orderedTwoPointLegEvent x) <
        (orderedTwoPointTimedEvents τ τ' σ).idxOf (orderedTwoPointLegEvent y) := by
    simpa [orderedTwoPointTimedEventPosition, orderedTwoPointTimedEventEquiv,
      List.Nodup.getEquivOfForallMemList] using hEvent
  have h := List.idxOf_flatMap_lt_of_idxOf_lt twoPointTimedEventAtomicLegs
    (orderedTwoPointTimedEvents τ τ' σ)
    (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y) x y
    (orderedTwoPointTimedEvents_nodup τ τ' σ)
    (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
    (orderedTwoPointTimedEvents_all_mem τ τ' σ (orderedTwoPointLegEvent x))
    (orderedTwoPointTimedEvents_all_mem τ τ' σ (orderedTwoPointLegEvent y))
    (orderedTwoPointLeg_mem_eventAtomicLegs x)
    (orderedTwoPointLeg_mem_eventAtomicLegs y) hEventIdx
  simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegs] using h

/-- For legs supported on distinct events, flattened atomic-leg order is exactly event order. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hxy : orderedTwoPointLegEvent x ≠ orderedTwoPointLegEvent y) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x) <
        orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) := by
  constructor
  · intro hLeg
    rcases lt_trichotomy
        (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x))
        (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) with
      hEvent | hEvent | hEvent
    · exact hEvent
    · exact (hxy ((orderedTwoPointTimedEventEquiv τ τ' σ).symm.injective hEvent)).elim
    · have hReverse :=
        mixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt τ τ' σ y x hEvent
      exact (lt_asymm hLeg hReverse).elim
  · exact mixedTimeOrderedAtomicLegPosition_lt_of_eventPosition_lt τ τ' σ x y

/-- The flattened atomic-leg order of two legs is determined by the relative order of their two
supporting events. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hEvent :
      (orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent x) <
          orderedTwoPointTimedEventPosition τ τ' σ (orderedTwoPointLegEvent y)) ↔
        (orderedTwoPointTimedEventPosition τ τ' υ (orderedTwoPointLegEvent x) <
          orderedTwoPointTimedEventPosition τ τ' υ (orderedTwoPointLegEvent y))) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ x <
        mixedTimeOrderedAtomicLegPosition τ τ' υ y) := by
  classical
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  by_cases hxy : orderedTwoPointLegEvent x = orderedTwoPointLegEvent y
  · let event := orderedTwoPointLegEvent x
    have hx : x ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event] using orderedTwoPointLeg_mem_eventAtomicLegs x
    have hy : y ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event, hxy] using orderedTwoPointLeg_mem_eventAtomicLegs y
    have hσ := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' σ) event x y
      (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ event) hx hy
    have hυ := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' υ) event x y
      (mixedTimeOrderedAtomicLegs_nodup τ τ' υ)
      (orderedTwoPointTimedEvents_all_mem τ τ' υ event) hx hy
    calc
      mixedTimeOrderedAtomicLegPosition τ τ' σ x <
          mixedTimeOrderedAtomicLegPosition τ τ' σ y ↔
        (twoPointTimedEventAtomicLegs event).idxOf x <
          (twoPointTimedEventAtomicLegs event).idxOf y := by
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegs] using hσ
      _ ↔ mixedTimeOrderedAtomicLegPosition τ τ' υ x <
          mixedTimeOrderedAtomicLegPosition τ τ' υ y := by
            symm
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegs] using hυ
  · rw [mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' σ x y hxy,
      mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' υ x y hxy]
    exact hEvent

/-- The relative flattened positions of two standard legs depend only on the times of their two
supporting events and on their fixed local leg coordinates. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventTime_eq {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hxTime : twoPointTimedEventTime τ τ' σ (orderedTwoPointLegEvent x) =
      twoPointTimedEventTime τ τ' υ (orderedTwoPointLegEvent x))
    (hyTime : twoPointTimedEventTime τ τ' σ (orderedTwoPointLegEvent y) =
      twoPointTimedEventTime τ τ' υ (orderedTwoPointLegEvent y)) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ x <
        mixedTimeOrderedAtomicLegPosition τ τ' υ y) :=
  mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff τ τ' σ υ x y
    (orderedTwoPointTimedEventPosition_lt_iff_of_eventTime_eq
      τ τ' σ υ (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y) hxTime hyTime)

variable {m n : ℕ} {f : Fin m → Fin n}

/-- Transport a standard two-point leg along a reindexing of the interaction slots. -/
def orderedTwoPointLegMap (f : Fin m → Fin n) : OrderedTwoPointLeg m → OrderedTwoPointLeg n :=
  Sum.map id <| Prod.map (fun v => ⟨f (v : Fin m), Finset.mem_univ _⟩) id

@[simp]
theorem orderedTwoPointLegMap_inl (f : Fin m → Fin n) (e : Fin 2) :
    orderedTwoPointLegMap f (Sum.inl e) = Sum.inl e := rfl

@[simp]
theorem orderedTwoPointLegMap_inr (f : Fin m → Fin n)
    (v : ↥(Finset.univ : Finset (Fin m))) (l : Fin 4) :
    orderedTwoPointLegMap f (Sum.inr (v, l)) =
      Sum.inr (⟨f (v : Fin m), Finset.mem_univ _⟩, l) := rfl

/-- An injective reindexing of the slots transports distinct legs to distinct legs. -/
theorem orderedTwoPointLegMap_injective (hf : Function.Injective f) :
    Function.Injective (orderedTwoPointLegMap f) := by
  unfold orderedTwoPointLegMap
  apply Function.Injective.sumMap
  · exact Function.injective_id
  · apply Function.Injective.prodMap
    · intro v w h
      exact Subtype.ext (hf (congrArg Subtype.val h))
    · exact Function.injective_id

/-- The transported leg is supported on the transported event. -/
@[simp]
theorem orderedTwoPointLegEvent_orderedTwoPointLegMap (f : Fin m → Fin n)
    (leg : OrderedTwoPointLeg m) :
    orderedTwoPointLegEvent (orderedTwoPointLegMap f leg) =
      twoPointTimedEventMap f (orderedTwoPointLegEvent leg) := by
  cases leg with
  | inl e => rfl
  | inr p => rfl

/-- The leg list of an event is relabeled, not reordered. -/
theorem twoPointTimedEventAtomicLegs_map (f : Fin m → Fin n) (event : TwoPointTimedEvent m) :
    twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event) =
      (twoPointTimedEventAtomicLegs event).map (orderedTwoPointLegMap f) := by
  cases event with
  | inl e => simp
  | inr v => simp

/-- The ambient mixed leg order restricts to the mixed leg order of a strictly monotone family of
interaction slots. -/
theorem mixedTimeOrderedAtomicLegPosition_map_lt_iff (hf : StrictMono f) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (x y : OrderedTwoPointLeg m) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedTwoPointLegMap f x) <
        mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedTwoPointLegMap f y)) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' (σ ∘ f) x <
        mixedTimeOrderedAtomicLegPosition τ τ' (σ ∘ f) y) := by
  classical
  letI : BEq (OrderedTwoPointLeg m) := instBEqOfDecidableEq
  letI : BEq (OrderedTwoPointLeg n) := instBEqOfDecidableEq
  have hInj := orderedTwoPointLegMap_injective hf.injective
  by_cases hxy : orderedTwoPointLegEvent x = orderedTwoPointLegEvent y
  · let event := orderedTwoPointLegEvent x
    have hx : x ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event] using orderedTwoPointLeg_mem_eventAtomicLegs x
    have hy : y ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event, hxy] using orderedTwoPointLeg_mem_eventAtomicLegs y
    have hxMap : orderedTwoPointLegMap f x ∈
        twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event) := by
      rw [twoPointTimedEventAtomicLegs_map]
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    have hyMap : orderedTwoPointLegMap f y ∈
        twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event) := by
      rw [twoPointTimedEventAtomicLegs_map]
      exact List.mem_map.2 ⟨y, hy, rfl⟩
    have hPiece := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' (σ ∘ f)) event x y
      (mixedTimeOrderedAtomicLegs_nodup τ τ' (σ ∘ f))
      (orderedTwoPointTimedEvents_all_mem τ τ' (σ ∘ f) event) hx hy
    have hAmbient := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' σ) (twoPointTimedEventMap f event)
      (orderedTwoPointLegMap f x) (orderedTwoPointLegMap f y)
      (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ (twoPointTimedEventMap f event)) hxMap hyMap
    have hidx (z : OrderedTwoPointLeg m) :
        ((twoPointTimedEventAtomicLegs event).map (orderedTwoPointLegMap f)).idxOf
            (orderedTwoPointLegMap f z) =
          (twoPointTimedEventAtomicLegs event).idxOf z := by
      unfold List.idxOf
      rw [List.findIdx_map]
      apply congrArg (fun p => (twoPointTimedEventAtomicLegs event).findIdx p)
      funext w
      simp [hInj.eq_iff]
    calc
      mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedTwoPointLegMap f x) <
            mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedTwoPointLegMap f y) ↔
          (twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event)).idxOf
              (orderedTwoPointLegMap f x) <
            (twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event)).idxOf
              (orderedTwoPointLegMap f y) := by
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegs] using hAmbient
      _ ↔ (twoPointTimedEventAtomicLegs event).idxOf x <
            (twoPointTimedEventAtomicLegs event).idxOf y := by
            rw [twoPointTimedEventAtomicLegs_map, hidx x, hidx y]
      _ ↔ mixedTimeOrderedAtomicLegPosition τ τ' (σ ∘ f) x <
            mixedTimeOrderedAtomicLegPosition τ τ' (σ ∘ f) y := by
            symm
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegs] using hPiece
  · have hxyMap : orderedTwoPointLegEvent (orderedTwoPointLegMap f x) ≠
        orderedTwoPointLegEvent (orderedTwoPointLegMap f y) := by
      rw [orderedTwoPointLegEvent_orderedTwoPointLegMap,
        orderedTwoPointLegEvent_orderedTwoPointLegMap]
      exact fun hEq => hxy (twoPointTimedEventMap_injective hf.injective hEq)
    rw [mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' σ _ _ hxyMap,
      mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt τ τ' (σ ∘ f) x y hxy,
      orderedTwoPointLegEvent_orderedTwoPointLegMap,
      orderedTwoPointLegEvent_orderedTwoPointLegMap,
      orderedTwoPointTimedEventPosition_map_lt_iff hf]

end Common
end SecondQuantization
