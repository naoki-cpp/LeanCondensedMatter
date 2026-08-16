import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered

set_option linter.style.header false

/-!
# Quartic legs inside the mixed two-point order

A quartic component contributes only interaction legs. This module embeds its fixed ordered quartic
leg enumeration into the mixed two-point atomic order and records the exact monotonicity used by
component factorizations.

The construction is purely combinatorial and independent of particle statistics, contraction
kernels, or operator realizations.
-/

namespace SecondQuantization
namespace Common

/-- View a leg in the fixed ordered quartic enumeration as the corresponding interaction leg of a
two-point enumeration with the same interaction slots. -/
noncomputable def orderedQuarticLegToTwoPointLeg {n : ℕ}
    (p : Fin (2 * (2 * n))) : OrderedTwoPointLeg n :=
  let q := orderedQuarticLegEquiv n p
  Sum.inr (⟨q.1, Finset.mem_univ q.1⟩, q.2)

@[simp]
theorem orderedQuarticLegToTwoPointLeg_orderedQuarticLegEquiv_symm
    {n : ℕ} (v : Fin n) (l : Fin 4) :
    orderedQuarticLegToTwoPointLeg ((orderedQuarticLegEquiv n).symm (v, l)) =
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
  let pa := orderedQuarticLegEquiv n a
  let pb := orderedQuarticLegEquiv n b
  have hab' :
      (orderedQuarticLegEquiv n).symm pa <
        (orderedQuarticLegEquiv n).symm pb := by
    simpa [pa, pb] using hab
  let x : OrderedTwoPointLeg n := Sum.inr (⟨pa.1, Finset.mem_univ pa.1⟩, pa.2)
  let y : OrderedTwoPointLeg n := Sum.inr (⟨pb.1, Finset.mem_univ pb.1⟩, pb.2)
  change mixedTimeOrderedAtomicLegPosition τ τ' σ x <
    mixedTimeOrderedAtomicLegPosition τ τ' σ y
  by_cases hslot : pa.1 = pb.1
  · have hlocal : pa.2 < pb.2 := by
      apply (orderedQuarticLegEquiv_symm_lt_symm_iff_snd_lt n pa.1 pa.2 pb.2).1
      simpa [hslot] using hab'
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
  · have hslotLt : pa.1 < pb.1 :=
      (orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne
        n pa.1 pb.1 pa.2 pb.2 hslot).1 hab'
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

/-- Ambient mixed position of a fixed-order quartic leg after embedding its local interaction slots. -/
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

end Common
end SecondQuantization
