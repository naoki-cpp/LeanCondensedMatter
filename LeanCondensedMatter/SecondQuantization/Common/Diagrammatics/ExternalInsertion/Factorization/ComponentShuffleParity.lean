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
  have hvw :
      d.ambientInteractionVertex B v ≠ d.ambientInteractionVertex C w := by
    intro hvw
    apply hBC
    apply interactionSector_component_unique d.vertexGraph
      (d.ambientInteractionVertex B v) B C
    · exact v.2
    · have hvwVal : (v.1 : Fin N) = w.1 :=
        congrArg Subtype.val hvw
      change (v.1 : Fin N) ∈
        interactionSector (C : Finset (ExternalInsertionVertex E S))
      rw [hvwVal]
      exact w.2
  rw [externalInsertionInteractionLeg_lt_iff]
  simp [hvw.symm]

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
    simp only [Fin.lt_def, externalInsertionExternalLeg_val]
  have hzero :
      (∑ q : ↥(interactionSector
          (C : Finset (ExternalInsertionVertex E S))) × Fin 4,
        if d.componentLegPosition C (Sum.inr q) <
          d.componentLegPosition B (Sum.inl e) then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [ite_eq_right (not_lt_of_ge (le_of_lt
      (d.componentExternal_lt_interaction C B e q.1 q.2)))]
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
          rw [ite_eq_left (d.componentExternal_lt_interaction B C e v l)]
        _ = 2 * d.externalPairCount C := by simp
    rw [hext]
    exact ⟨d.externalPairCount C, by omega⟩
  · have hdiv := Fintype.dvd_sum_equiv_fst_of_dvd_card
      (Equiv.refl (↥(interactionSector
        (C : Finset (ExternalInsertionVertex E S))) × Fin 4))
      (fun w => if d.ambientInteractionVertex C w <
        d.ambientInteractionVertex B v then (1 : ℕ) else 0)
      (by decide : 2 ∣ Fintype.card (Fin 4))
    convert hdiv using 1
    apply Finset.sum_congr rfl
    rintro ⟨w, k⟩ _
    simp only [Equiv.refl_apply, d.componentInteractionLeg_lt_iff B C hBC v l w k]
    by_cases hlt : d.ambientInteractionVertex C w < d.ambientInteractionVertex B v <;>
      simp [hlt]

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
      d.componentExternalShuffle blockOrder (fun B C hBC => by
          classical
          rw [d.componentLegShuffle_blockInversionCount_eq_sum B C hBC,
            d.componentExternalShuffle_blockInversionCount_eq_sum B C hBC]
          rw [Fintype.sum_sum_type]
          have hext :
              (∑ e : Fin (2 * d.externalPairCount B),
                d.componentLegInversionInner B C (Sum.inl e)) =
                ∑ e : Fin (2 * d.externalPairCount B),
                  d.componentExternalInversionInner B C e :=
            Finset.sum_congr rfl (fun e _ =>
              d.componentLegInversionInner_external B C e)
          have hint :
              (∑ p : ↥(interactionSector
                  (B : Finset (ExternalInsertionVertex E S))) × Fin 4,
                d.componentLegInversionInner B C (Sum.inr p)) % 2 = 0 := by
            apply Nat.mod_eq_zero_of_dvd
            refine Finset.dvd_sum fun p _ => ?_
            exact Nat.dvd_of_mod_eq_zero
              (d.componentLegInversionInner_interaction_mod_two B C hBC p.1 p.2)
          rw [hext]
          unfold Nat.ModEq
          rw [Nat.add_mod, hint, add_zero, Nat.mod_mod])
  simpa [Nat.ModEq] using h

end Common
end SecondQuantization
