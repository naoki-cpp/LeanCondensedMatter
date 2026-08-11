import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedEventBlockOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedEventSlotEmbedding

set_option linter.style.header false

/-!
# Restricting the mixed leg order along a monotone family of interaction slots

A connected piece of a two-point diagram is itself a diagram, on as many interaction slots as it
owns. Its legs therefore have their own mixed positions, computed from its own slot indices and the
times it inherits, while the ambient diagram positions the same legs among all the legs. This module
shows the two orders agree.

Two ingredients combine. The supporting events are ordered the same way, because the slots are
reindexed monotonically. And legs supported on one event are ordered by that event's own leg list,
which the reindexing relabels injectively without moving anything: an external event carries a
single leg, and an interaction event carries its four legs in their fixed local order whatever its
slot index is.
-/

namespace SecondQuantization
namespace Fermionic

variable {m n : ℕ} {f : Fin m → Fin n}

/-- Transport a standard two-point leg along a reindexing of the interaction slots. -/
def orderedTwoPointLegMap (f : Fin m → Fin n) : OrderedTwoPointLeg m → OrderedTwoPointLeg n
  | .inl e => .inl e
  | .inr p => .inr (⟨f (p.1 : Fin m), Finset.mem_univ _⟩, p.2)

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
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b => simpa using hxy
      | inr q =>
          obtain ⟨w, l'⟩ := q
          simp at hxy
  | inr p =>
      obtain ⟨v, l⟩ := p
      cases y with
      | inl b => simp at hxy
      | inr q =>
          obtain ⟨w, l'⟩ := q
          simp only [orderedTwoPointLegMap_inr, Sum.inr.injEq, Prod.mk.injEq,
            Subtype.mk.injEq] at hxy
          obtain ⟨hv, hl⟩ := hxy
          subst hl
          exact congrArg (fun u => Sum.inr (u, l)) (Subtype.ext (hf hv))

/-- The transported leg is supported on the transported event. -/
@[simp]
theorem orderedTwoPointLegEvent_orderedTwoPointLegMap (f : Fin m → Fin n)
    (leg : OrderedTwoPointLeg m) :
    orderedTwoPointLegEvent (orderedTwoPointLegMap f leg) =
      twoPointTimedEventMap f (orderedTwoPointLegEvent leg) := by
  cases leg with
  | inl e => rfl
  | inr p => rfl

/-- **The leg list of an event is relabeled, not reordered.** An external event carries one leg and
an interaction event carries its four legs in their fixed local order, so reindexing the slot only
renames the entries. -/
theorem twoPointTimedEventAtomicLegs_map (f : Fin m → Fin n) (event : TwoPointTimedEvent m) :
    twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event) =
      (twoPointTimedEventAtomicLegs event).map (orderedTwoPointLegMap f) := by
  cases event with
  | inl e => simp
  | inr v => simp

/-- **The ambient mixed leg order restricts to the mixed leg order of the reindexed slots.** For a
strictly monotone reindexing of the interaction slots, two legs of the piece compare in the ambient
mixed order exactly as they compare in the piece's own mixed order. -/
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
    calc
      mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedTwoPointLegMap f x) <
            mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedTwoPointLegMap f y) ↔
          (twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event)).idxOf
              (orderedTwoPointLegMap f x) <
            (twoPointTimedEventAtomicLegs (twoPointTimedEventMap f event)).idxOf
              (orderedTwoPointLegMap f y) := by
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
              mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using hAmbient
      _ ↔ (twoPointTimedEventAtomicLegs event).idxOf x <
            (twoPointTimedEventAtomicLegs event).idxOf y := by
            rw [twoPointTimedEventAtomicLegs_map, List.idxOf_map_of_injective hInj,
              List.idxOf_map_of_injective hInj]
      _ ↔ mixedTimeOrderedAtomicLegPosition τ τ' (σ ∘ f) x <
            mixedTimeOrderedAtomicLegPosition τ τ' (σ ∘ f) y := by
            symm
            simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
              mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using hPiece
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

end Fermionic
end SecondQuantization
