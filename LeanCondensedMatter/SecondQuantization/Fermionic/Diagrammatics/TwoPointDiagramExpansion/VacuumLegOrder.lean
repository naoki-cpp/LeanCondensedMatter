import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedLegSlotEmbedding
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPairing

set_option linter.style.header false

/-!
# Quartic vacuum legs inside the mixed two-point order

A quartic vacuum piece contributes only interaction legs.  This module embeds its fixed ordered
quartic leg enumeration into the mixed two-point atomic order and records the exact monotonicity
needed by the external/vacuum linked-cluster factorization.

If the local interaction times are strictly decreasing in the fixed vertex order, the fixed quartic
leg order agrees with the relative mixed order of those interaction legs.  The statement is then
transported along any strictly monotone embedding of local interaction slots into ambient two-point
slots.
-/

namespace SecondQuantization
namespace Fermionic

open Common

/-- View a leg in the fixed ordered quartic enumeration as the corresponding interaction leg of a
two-point enumeration with the same interaction slots. -/
noncomputable def orderedQuarticLegToTwoPointLeg {n : ℕ}
    (p : Fin (2 * (2 * n))) : OrderedTwoPointLeg n :=
  let q := Common.orderedQuarticLegEquiv n p
  Sum.inr (⟨q.1, Finset.mem_univ q.1⟩, q.2)

@[simp]
theorem orderedQuarticLegToTwoPointLeg_orderedQuarticLegEquiv_symm
    {n : ℕ} (v : Fin n) (l : Fin 4) :
    orderedQuarticLegToTwoPointLeg ((Common.orderedQuarticLegEquiv n).symm (v, l)) =
      Sum.inr (⟨v, Finset.mem_univ v⟩, l) := by
  simp [orderedQuarticLegToTwoPointLeg]

private theorem twoPointTimedEventAtomicLegs_interaction_idxOf
    {n : ℕ} (v : Fin n) (hv : v ∈ (Finset.univ : Finset (Fin n))) (l : Fin 4) :
    @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq
        (Sum.inr (⟨v, hv⟩, l))
        (twoPointTimedEventAtomicLegs (Sum.inr v)) = l.val := by
  fin_cases l <;> simp [twoPointTimedEventAtomicLegs]

/-- Mixed two-point position occupied by a fixed-order quartic interaction leg. -/
noncomputable def mixedTimeOrderedQuarticLegPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    Fin (2 * (2 * n + 1)) :=
  mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedQuarticLegToTwoPointLeg p)

/-- When interaction times are strictly decreasing in slot order, the fixed ordered quartic leg
enumeration sits strictly increasingly inside the mixed two-point atomic order. -/
theorem mixedTimeOrderedQuarticLegPosition_strictMono_of_strictAnti {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (hσ : StrictAnti σ) :
    StrictMono (mixedTimeOrderedQuarticLegPosition τ τ' σ) := by
  intro a b hab
  let pa := Common.orderedQuarticLegEquiv n a
  let pb := Common.orderedQuarticLegEquiv n b
  have ha := Common.orderedQuarticLegEquiv_reconstruct_val n a
  have hb := Common.orderedQuarticLegEquiv_reconstruct_val n b
  change a.val = pa.2.val + 4 * pa.1.val at ha
  change b.val = pb.2.val + 4 * pb.1.val at hb
  change a.val < b.val at hab
  have hpa : pa.2.val < 4 := pa.2.isLt
  have hpb : pb.2.val < 4 := pb.2.isLt
  let x : OrderedTwoPointLeg n := Sum.inr (⟨pa.1, Finset.mem_univ pa.1⟩, pa.2)
  let y : OrderedTwoPointLeg n := Sum.inr (⟨pb.1, Finset.mem_univ pb.1⟩, pb.2)
  change mixedTimeOrderedAtomicLegPosition τ τ' σ x <
    mixedTimeOrderedAtomicLegPosition τ τ' σ y
  by_cases hslot : pa.1 = pb.1
  · have hlocal : pa.2.val < pb.2.val := by
      have hslotVal : pa.1.val = pb.1.val := congrArg Fin.val hslot
      omega
    have hEvent : orderedTwoPointLegEvent x = orderedTwoPointLegEvent y := by
      simp [x, y, hslot, orderedTwoPointLegEvent]
    let event := orderedTwoPointLegEvent x
    have hx : x ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event] using orderedTwoPointLeg_mem_eventAtomicLegs x
    have hy : y ∈ twoPointTimedEventAtomicLegs event := by
      simpa [event, hEvent] using orderedTwoPointLeg_mem_eventAtomicLegs y
    have hblock := List.idxOf_flatMap_block_lt_iff twoPointTimedEventAtomicLegs
      (orderedTwoPointTimedEvents τ τ' σ) event x y
      (mixedTimeOrderedAtomicLegs_nodup τ τ' σ)
      (orderedTwoPointTimedEvents_all_mem τ τ' σ event) hx hy
    have hidx :
        @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq x
            (twoPointTimedEventAtomicLegs event) <
          @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq y
            (twoPointTimedEventAtomicLegs event) := by
      have hleft :
          @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq x
              (twoPointTimedEventAtomicLegs event) = pa.2.val := by
        simpa [event, x, orderedTwoPointLegEvent, hslot] using
          (twoPointTimedEventAtomicLegs_interaction_idxOf
            pb.1 (Finset.mem_univ pb.1) pa.2)
      have hright :
          @List.idxOf (OrderedTwoPointLeg n) instBEqOfDecidableEq y
              (twoPointTimedEventAtomicLegs event) = pb.2.val := by
        simpa [event, x, y, orderedTwoPointLegEvent, hslot] using
          (twoPointTimedEventAtomicLegs_interaction_idxOf
            pb.1 (Finset.mem_univ pb.1) pb.2)
      rw [hleft, hright]
      exact hlocal
    simpa [mixedTimeOrderedAtomicLegPosition, mixedTimeOrderedAtomicLegEquiv,
      mixedTimeOrderedAtomicLegs, List.Nodup.getEquivOfForallMemList] using hblock.mpr hidx
  · have hslotLt : pa.1 < pb.1 := by
      have hslotNeVal : pa.1.val ≠ pb.1.val := by
        intro h
        exact hslot (Fin.ext h)
      omega
    have hEventNe : orderedTwoPointLegEvent x ≠ orderedTwoPointLegEvent y := by
      simp [x, y, orderedTwoPointLegEvent, hslot]
    apply (mixedTimeOrderedAtomicLegPosition_lt_iff_eventPosition_lt
      τ τ' σ x y hEventNe).2
    apply (orderedTwoPointTimedEventPosition_lt_iff τ τ' σ
      (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y)).2
    refine ⟨?_, hEventNe⟩
    left
    simpa [x, y, orderedTwoPointLegEvent, twoPointTimedEventTime] using hσ hslotLt

/-- Embed a fixed-order quartic leg through a monotone map from local interaction slots to ambient
two-point interaction slots. -/
noncomputable def orderedQuarticLegMapToTwoPointLeg {m n : ℕ} (f : Fin m → Fin n)
    (p : Fin (2 * (2 * m))) : OrderedTwoPointLeg n :=
  orderedTwoPointLegMap f (orderedQuarticLegToTwoPointLeg p)

/-- Ambient mixed position of a fixed-order quartic leg after embedding its local interaction slots.
-/
noncomputable def mixedTimeOrderedQuarticLegMapPosition {m n : ℕ}
    (f : Fin m → Fin n) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * m))) : Fin (2 * (2 * n + 1)) :=
  mixedTimeOrderedAtomicLegPosition τ τ' σ (orderedQuarticLegMapToTwoPointLeg f p)

/-- A strictly monotone slot embedding preserves the fixed quartic leg order whenever the inherited
local interaction times are strictly decreasing. -/
theorem mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
    {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (hσ : StrictAnti (σ ∘ f)) :
    StrictMono (mixedTimeOrderedQuarticLegMapPosition f τ τ' σ) := by
  intro a b hab
  change mixedTimeOrderedAtomicLegPosition τ τ' σ
      (orderedTwoPointLegMap f (orderedQuarticLegToTwoPointLeg a)) <
    mixedTimeOrderedAtomicLegPosition τ τ' σ
      (orderedTwoPointLegMap f (orderedQuarticLegToTwoPointLeg b))
  rw [mixedTimeOrderedAtomicLegPosition_map_lt_iff hf]
  exact mixedTimeOrderedQuarticLegPosition_strictMono_of_strictAnti
    τ τ' (σ ∘ f) hσ hab

end Fermionic
end SecondQuantization
