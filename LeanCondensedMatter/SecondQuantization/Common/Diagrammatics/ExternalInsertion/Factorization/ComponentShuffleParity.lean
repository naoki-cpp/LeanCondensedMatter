import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct
import Mathlib.Algebra.BigOperators.ModEq

set_option linter.style.header false

/-!
# External-sector parity of component leg shuffles

The canonical flattened leg order places all external insertions before all quartic interaction
legs. Each interaction vertex contributes a consecutive block of four legs. Consequently the
inter-component inversion parity of the full component-leg shuffle is determined entirely by the
one-legged external sectors.

This file keeps that reduction statistics-independent. Fermionic time-order signs consume the
result downstream.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

private def ExternalInsertionDiagram.ambientInteractionVertex
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) : ↥S :=
  ⟨v.1, interactionSector_subset
    (B : Finset (ExternalInsertionVertex E S)) v.2⟩

private noncomputable def ExternalInsertionDiagram.componentLegPosition
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (p : ExternalInsertionLeg (d.externalPairCount B)
      (interactionSector (B : Finset (ExternalInsertionVertex E S)))) :
    Fin (2 * (2 * S.card + E)) :=
  d.componentDiagramLeg B
    ((externalInsertionLegEquiv (d.externalPairCount B)
      (interactionSector (B : Finset (ExternalInsertionVertex E S)))).symm p)

@[simp]
private theorem ExternalInsertionDiagram.componentLegPosition_external
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount B)) :
    d.componentLegPosition B (Sum.inl e) =
      externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1 := by
  change d.componentDiagramLeg B
      (externalInsertionExternalLeg (d.externalPairCount B)
        (interactionSector (B : Finset (ExternalInsertionVertex E S))) e) = _
  exact d.componentDiagramLeg_external B e

@[simp]
private theorem ExternalInsertionDiagram.componentLegPosition_interaction
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.vertexGraph.componentPartition.parts)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) (l : Fin 4) :
    d.componentLegPosition B (Sum.inr (v, l)) =
      externalInsertionInteractionLeg (E := E) (d.ambientInteractionVertex B v) l := by
  change d.componentDiagramLeg B
      (externalInsertionInteractionLeg (E := d.externalPairCount B) v l) = _
  exact d.componentDiagramLeg_interaction B v l

private theorem ExternalInsertionDiagram.ambientInteractionVertex_ne
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S))))
    (w : ↥(interactionSector
      (C : Finset (ExternalInsertionVertex E S)))) :
    d.ambientInteractionVertex B v ≠ d.ambientInteractionVertex C w := by
  intro hvw
  have hvB :
      (Sum.inr (d.ambientInteractionVertex B v) : ExternalInsertionVertex E S) ∈
        (B : Finset (ExternalInsertionVertex E S)) :=
    (mem_interactionSector_subtype
      (B : Finset (ExternalInsertionVertex E S))
      (d.ambientInteractionVertex B v)).1 v.2
  have hwC :
      (Sum.inr (d.ambientInteractionVertex C w) : ExternalInsertionVertex E S) ∈
        (C : Finset (ExternalInsertionVertex E S)) :=
    (mem_interactionSector_subtype
      (C : Finset (ExternalInsertionVertex E S))
      (d.ambientInteractionVertex C w)).1 w.2
  have hvC :
      (Sum.inr (d.ambientInteractionVertex B v) : ExternalInsertionVertex E S) ∈
        (C : Finset (ExternalInsertionVertex E S)) := by
    simpa only [hvw] using hwC
  have hB :
      d.vertexGraph.componentBlock
          (Sum.inr (d.ambientInteractionVertex B v)) =
        (B : Finset (ExternalInsertionVertex E S)) :=
    (d.vertexGraph.componentBlock_eq_iff_mem B.2 _).2 hvB
  have hC :
      d.vertexGraph.componentBlock
          (Sum.inr (d.ambientInteractionVertex B v)) =
        (C : Finset (ExternalInsertionVertex E S)) :=
    (d.vertexGraph.componentBlock_eq_iff_mem C.2 _).2 hvC
  apply hBC
  exact Subtype.ext (hB.symm.trans hC)

private theorem ExternalInsertionDiagram.componentInteractionLeg_lt_iff
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) (l : Fin 4)
    (w : ↥(interactionSector
      (C : Finset (ExternalInsertionVertex E S)))) (k : Fin 4) :
    d.componentLegPosition C (Sum.inr (w, k)) <
        d.componentLegPosition B (Sum.inr (v, l)) ↔
      d.ambientInteractionVertex C w < d.ambientInteractionVertex B v := by
  rw [d.componentLegPosition_interaction, d.componentLegPosition_interaction]
  change
    (externalInsertionInteractionLeg (E := E) (d.ambientInteractionVertex C w) k).val <
        (externalInsertionInteractionLeg (E := E) (d.ambientInteractionVertex B v) l).val ↔
      d.ambientInteractionVertex C w < d.ambientInteractionVertex B v
  simp only [externalInsertionInteractionLeg_val]
  have hvw :
      d.ambientInteractionVertex B v ≠ d.ambientInteractionVertex C w :=
    d.ambientInteractionVertex_ne B C hBC v w
  have hrank_ne :
      ((S.orderIsoOfFin rfl).symm (d.ambientInteractionVertex C w)).val ≠
        ((S.orderIsoOfFin rfl).symm (d.ambientInteractionVertex B v)).val := by
    intro h
    apply hvw
    apply (S.orderIsoOfFin rfl).symm.injective
    exact Fin.ext h.symm
  constructor
  · intro h
    have hk : k.val < 4 := k.isLt
    have hl : l.val < 4 := l.isLt
    have hrank :
        ((S.orderIsoOfFin rfl).symm (d.ambientInteractionVertex C w)).val <
          ((S.orderIsoOfFin rfl).symm (d.ambientInteractionVertex B v)).val := by
      omega
    simpa using (S.orderIsoOfFin rfl).strictMono hrank
  · intro h
    have hrank :
        ((S.orderIsoOfFin rfl).symm (d.ambientInteractionVertex C w)).val <
          ((S.orderIsoOfFin rfl).symm (d.ambientInteractionVertex B v)).val := by
      simpa using (S.orderIsoOfFin rfl).symm.strictMono h
    have hk : k.val < 4 := k.isLt
    have hl : l.val < 4 := l.isLt
    omega

private theorem ExternalInsertionDiagram.componentExternal_lt_interaction
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount C))
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) (l : Fin 4) :
    d.componentLegPosition C (Sum.inl e) <
      d.componentLegPosition B (Sum.inr (v, l)) := by
  rw [d.componentLegPosition_external, d.componentLegPosition_interaction]
  change
    (externalInsertionExternalLeg E S (d.externalSectorOrderIso C e).1).val <
      (externalInsertionInteractionLeg (E := E) (d.ambientInteractionVertex B v) l).val
  rw [externalInsertionExternalLeg_val, externalInsertionInteractionLeg_val]
  have he := (d.externalSectorOrderIso C e).1.isLt
  omega

private theorem ExternalInsertionDiagram.componentInteraction_not_lt_external
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts)
    (v : ↥(interactionSector
      (C : Finset (ExternalInsertionVertex E S)))) (l : Fin 4)
    (e : Fin (2 * d.externalPairCount B)) :
    ¬ d.componentLegPosition C (Sum.inr (v, l)) <
      d.componentLegPosition B (Sum.inl e) := by
  rw [d.componentLegPosition_interaction, d.componentLegPosition_external]
  change
    ¬ (externalInsertionInteractionLeg (E := E) (d.ambientInteractionVertex C v) l).val <
      (externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1).val
  rw [externalInsertionExternalLeg_val, externalInsertionInteractionLeg_val]
  have he := (d.externalSectorOrderIso B e).1.isLt
  omega

private noncomputable def ExternalInsertionDiagram.componentLegInversionInner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts)
    (p : ExternalInsertionLeg (d.externalPairCount B)
      (interactionSector (B : Finset (ExternalInsertionVertex E S)))) : ℕ :=
  ∑ q : ExternalInsertionLeg (d.externalPairCount C)
      (interactionSector (C : Finset (ExternalInsertionVertex E S))),
    if d.componentLegPosition C q < d.componentLegPosition B p then 1 else 0

private noncomputable def ExternalInsertionDiagram.componentExternalInversionInner
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount B)) : ℕ :=
  ∑ f : Fin (2 * d.externalPairCount C),
    if (d.externalSectorOrderIso C f).1 < (d.externalSectorOrderIso B e).1 then 1 else 0

private theorem ExternalInsertionDiagram.componentLegInversionInner_external
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts)
    (e : Fin (2 * d.externalPairCount B)) :
    d.componentLegInversionInner B C (Sum.inl e) =
      d.componentExternalInversionInner B C e := by
  classical
  unfold ExternalInsertionDiagram.componentLegInversionInner
    ExternalInsertionDiagram.componentExternalInversionInner
  rw [Fintype.sum_sum_type]
  have hext :
      (∑ f : Fin (2 * d.externalPairCount C),
        if d.componentLegPosition C (Sum.inl f) <
          d.componentLegPosition B (Sum.inl e) then 1 else 0) =
        ∑ f : Fin (2 * d.externalPairCount C),
          if (d.externalSectorOrderIso C f).1 <
            (d.externalSectorOrderIso B e).1 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro f _
    rw [d.componentLegPosition_external, d.componentLegPosition_external]
    by_cases hlt :
        (d.externalSectorOrderIso C f).1 < (d.externalSectorOrderIso B e).1
    · have hltVal :
          (d.externalSectorOrderIso C f).1.val <
            (d.externalSectorOrderIso B e).1.val := by
        exact hlt
      have hleg :
          externalInsertionExternalLeg E S (d.externalSectorOrderIso C f).1 <
            externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1 := by
        change
          (externalInsertionExternalLeg E S (d.externalSectorOrderIso C f).1).val <
            (externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1).val
        exact hltVal
      rw [if_pos hleg, if_pos hlt]
    · have hltVal :
          ¬ (d.externalSectorOrderIso C f).1.val <
            (d.externalSectorOrderIso B e).1.val := by
        intro h
        apply hlt
        exact h
      have hleg :
          ¬ externalInsertionExternalLeg E S (d.externalSectorOrderIso C f).1 <
            externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1 := by
        intro h
        apply hltVal
        change
          (externalInsertionExternalLeg E S (d.externalSectorOrderIso C f).1).val <
            (externalInsertionExternalLeg E S (d.externalSectorOrderIso B e).1).val at h
        exact h
      rw [if_neg hleg, if_neg hlt]
  have hzero :
      (∑ q : ↥(interactionSector
          (C : Finset (ExternalInsertionVertex E S))) × Fin 4,
        if d.componentLegPosition C (Sum.inr q) <
          d.componentLegPosition B (Sum.inl e) then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg (d.componentInteraction_not_lt_external B C q.1 q.2 e)]
  rw [hext, hzero, add_zero]

private theorem ExternalInsertionDiagram.componentLegInversionInner_interaction_mod_two
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C)
    (v : ↥(interactionSector
      (B : Finset (ExternalInsertionVertex E S)))) (l : Fin 4) :
    d.componentLegInversionInner B C (Sum.inr (v, l)) % 2 = 0 := by
  classical
  unfold ExternalInsertionDiagram.componentLegInversionInner
  rw [Fintype.sum_sum_type]
  apply Nat.mod_eq_zero_of_dvd
  apply dvd_add
  · have hext :
        (∑ e : Fin (2 * d.externalPairCount C),
          if d.componentLegPosition C (Sum.inl e) <
            d.componentLegPosition B (Sum.inr (v, l)) then 1 else 0) =
          2 * d.externalPairCount C := by
      calc
        _ = ∑ _e : Fin (2 * d.externalPairCount C), 1 := by
          apply Finset.sum_congr rfl
          intro e _
          rw [if_pos (d.componentExternal_lt_interaction B C e v l)]
        _ = 2 * d.externalPairCount C := by simp
    rw [hext]
    exact ⟨d.externalPairCount C, by omega⟩
  · rw [Fintype.sum_prod_type]
    refine Finset.dvd_sum fun w _ => ?_
    have hcount :
        (∑ k : Fin 4,
          if d.componentLegPosition C (Sum.inr (w, k)) <
            d.componentLegPosition B (Sum.inr (v, l)) then 1 else 0) =
          4 * (if d.ambientInteractionVertex C w <
            d.ambientInteractionVertex B v then 1 else 0) := by
      calc
        _ = ∑ _k : Fin 4,
            (if d.ambientInteractionVertex C w <
              d.ambientInteractionVertex B v then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hlt :
              d.ambientInteractionVertex C w < d.ambientInteractionVertex B v
          · have hfull :=
              (d.componentInteractionLeg_lt_iff B C hBC v l w k).2 hlt
            rw [if_pos hfull, if_pos hlt]
          · have hfull :
                ¬ d.componentLegPosition C (Sum.inr (w, k)) <
                  d.componentLegPosition B (Sum.inr (v, l)) := by
              intro h
              exact hlt ((d.componentInteractionLeg_lt_iff B C hBC v l w k).1 h)
            rw [if_neg hfull, if_neg hlt]
        _ = 4 * (if d.ambientInteractionVertex C w <
              d.ambientInteractionVertex B v then 1 else 0) := by
          simp
    rw [hcount]
    refine ⟨2 * (if d.ambientInteractionVertex C w <
      d.ambientInteractionVertex B v then 1 else 0), ?_⟩
    ring

private theorem ExternalInsertionDiagram.componentLegShuffle_blockInversionCount_eq_sum
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C) :
    d.componentLegShuffle.blockInversionCount B C =
      ∑ p : ExternalInsertionLeg (d.externalPairCount B)
          (interactionSector (B : Finset (ExternalInsertionVertex E S))),
        d.componentLegInversionInner B C p := by
  classical
  rw [d.componentLegShuffle.blockInversionCount_of_ne hBC]
  simp only [ExternalInsertionDiagram.componentLegShuffle_slotEquiv_apply]
  rw [← Equiv.sum_comp
    (externalInsertionLegEquiv (d.externalPairCount B)
      (interactionSector (B : Finset (ExternalInsertionVertex E S)))).symm]
  apply Finset.sum_congr rfl
  intro p _
  unfold ExternalInsertionDiagram.componentLegInversionInner
  rw [← Equiv.sum_comp
    (externalInsertionLegEquiv (d.externalPairCount C)
      (interactionSector (C : Finset (ExternalInsertionVertex E S)))).symm]
  rfl

private theorem ExternalInsertionDiagram.componentExternalShuffle_blockInversionCount_eq_sum
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C) :
    d.componentExternalShuffle.blockInversionCount B C =
      ∑ e : Fin (2 * d.externalPairCount B),
        d.componentExternalInversionInner B C e := by
  classical
  rw [d.componentExternalShuffle.blockInversionCount_of_ne hBC]
  simp only [ExternalInsertionDiagram.componentExternalShuffle_slotEquiv_apply]
  rfl

/-- For two distinct connected components, the full flattened-leg interleaving and the
external-only interleaving have the same inversion parity. -/
theorem ExternalInsertionDiagram.componentLegShuffle_blockInversionCount_modEq_two_external
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B C : d.vertexGraph.componentPartition.parts) (hBC : B ≠ C) :
    Nat.ModEq 2
      (d.componentLegShuffle.blockInversionCount B C)
      (d.componentExternalShuffle.blockInversionCount B C) := by
  classical
  rw [d.componentLegShuffle_blockInversionCount_eq_sum B C hBC,
    d.componentExternalShuffle_blockInversionCount_eq_sum B C hBC]
  let g : ExternalInsertionLeg (d.externalPairCount B)
      (interactionSector (B : Finset (ExternalInsertionVertex E S))) → ℕ
    | Sum.inl e => d.componentExternalInversionInner B C e
    | Sum.inr _ => 0
  have hmod :
      Nat.ModEq 2
        (∑ p : ExternalInsertionLeg (d.externalPairCount B)
          (interactionSector (B : Finset (ExternalInsertionVertex E S))),
          d.componentLegInversionInner B C p)
        (∑ p : ExternalInsertionLeg (d.externalPairCount B)
          (interactionSector (B : Finset (ExternalInsertionVertex E S))), g p) := by
    refine Nat.ModEq.sum (n := 2) ?_
    intro p _
    cases p with
    | inl e =>
        simp only [g]
        rw [d.componentLegInversionInner_external B C e]
    | inr p =>
        rcases p with ⟨v, l⟩
        simpa [Nat.ModEq, g] using
          d.componentLegInversionInner_interaction_mod_two B C hBC v l
  have hg :
      (∑ p : ExternalInsertionLeg (d.externalPairCount B)
        (interactionSector (B : Finset (ExternalInsertionVertex E S))), g p) =
        ∑ e : Fin (2 * d.externalPairCount B),
          d.componentExternalInversionInner B C e := by
    rw [Fintype.sum_sum_type]
    simp [g]
  rw [← hg]
  exact hmod

/-- The total ordered inter-component inversion parity of the full component-leg shuffle is exactly
the parity of the external-only component shuffle. -/
theorem ExternalInsertionDiagram.componentLegShuffle_orderedBlockInversionCount_mod_two_eq_external
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (blockOrder :
      d.vertexGraph.componentPartition.parts ≃
        Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.componentLegShuffle.orderedBlockInversionCount blockOrder % 2 =
      d.componentExternalShuffle.orderedBlockInversionCount blockOrder % 2 := by
  have h :=
    d.componentLegShuffle.orderedBlockInversionCount_modEq_of_blockInversionCount_modEq
      d.componentExternalShuffle blockOrder
      (fun B C hBC =>
        d.componentLegShuffle_blockInversionCount_modEq_two_external B C hBC)
  simpa [Nat.ModEq] using h

end Common
end SecondQuantization
