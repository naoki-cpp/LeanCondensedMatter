import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumComponents

set_option linter.style.header false

/-!
# Image of the slot-split vacuum pair embedding

The fixed-order normalized pairs of a quartic vacuum piece embed into the mixed pairing of the
reassembled two-point diagram. This module identifies their image with exactly the ambient mixed
pairs carried by vacuum components and packages the resulting equivalence. The generic mixed
vacuum-pair type, component-fiber sum, and pair-cardinality facts are owned by
`TwoPoint.Mixed.MixedComponentPairEquiv`, independently of slot splitting.

The construction is purely combinatorial and is stated for arbitrary external/internal labels.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {n : ℕ}

/-- The first endpoint of an embedded quartic vacuum pair lies in the ambient component generated
by the corresponding right-side quartic vertex. -/
theorem TwoPointDiagram.ofSlotSplitVacuumNormalizedPairEmbedding_component
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let q := orderedLegToDiagramLeg
      ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) pr.1.1
    d.mixedPairComponent τ τ' σ
        (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
          T ext vac τ τ' σ hσ pr) =
      ⟨d.vertexGraph.componentBlock (slotSplitVacuumVertex (vertexOfLeg q)),
        d.vertexGraph.componentBlock_mem_componentPartition
          (slotSplitVacuumVertex (vertexOfLeg q))⟩ := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let p := pr.1.1
  let q := orderedLegToDiagramLeg
    ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) p
  have hleg :
      mixedTimeAmbientPositionEquiv τ τ' σ
          (mixedTimeOrderedQuarticLegMapPosition
            (slotSplitVacuumSlot T) τ τ' σ p) =
        slotLegSplitting (Finset.subset_univ T) (Sum.inr q) := by
    apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
    rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
    change mixedTimeOrderedAtomicLegEquiv τ τ' σ
        (mixedTimeOrderedAtomicLegPosition τ τ' σ
          (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p)) = _
    rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
    simpa only [Equiv.apply_symm_apply] using
      congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
        (slotSplitVacuumOrderedLeg_eq_slotSplitRight T p)
  have hvertex :
      twoPointVertexOfLeg
          (mixedTimeAmbientPositionEquiv τ τ' σ
            (mixedTimeOrderedQuarticLegMapPosition
              (slotSplitVacuumSlot T) τ τ' σ p)) =
        slotSplitVacuumVertex (vertexOfLeg q) := by
    rw [hleg, twoPointVertexOfLeg_slotLegSplitting_inr_exact]
  apply Subtype.ext
  change d.vertexGraph.componentBlock
      (twoPointVertexOfLeg
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
            T ext vac τ τ' σ hσ pr).1.1)) = _
  rw [TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_apply]
  exact congrArg d.vertexGraph.componentBlock hvertex

/-- The quartic normalized-pair embedding with codomain restricted to ambient vacuum-component
pairs. -/
private noncomputable def TwoPointDiagram.slotSplitVacuumMixedPairEmbedding
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair ↪
      (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ where
  toFun pr :=
    ⟨TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ pr,
      by
        rw [TwoPointDiagram.ofSlotSplitVacuumNormalizedPairEmbedding_component
          T ext vac τ τ' σ hσ pr]
        exact componentBlock_slotSplitVacuumVertex_mem_vacuumComponentParts
          (Finset.subset_univ T) ext vac
          (vertexOfLeg (orderedLegToDiagramLeg
            ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) pr.1.1))⟩
  inj' := by
    intro p q hpq
    apply (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ).injective
    exact congrArg Subtype.val hpq

/-- Under external connectedness, every ambient mixed pair lying in a vacuum component comes from a
unique normalized pair of the standalone quartic vacuum pairing. -/
private theorem TwoPointDiagram.slotSplitVacuumMixedPairEmbedding_surjective
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    Function.Surjective
      (TwoPointDiagram.slotSplitVacuumMixedPairEmbedding T ext vac τ τ' σ hσ) := by
  let emb := TwoPointDiagram.slotSplitVacuumMixedPairEmbedding T ext vac τ τ' σ hσ
  have hsource :
      Fintype.card (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair =
        2 * ((Finset.univ : Finset (Fin n)) \ T).card := by
    simpa using (vac.pairingInOrder (slotSplitVacuumOrder T)).card_normalizedPair
  have htarget :
      Fintype.card
          ((TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ) =
        2 * ((Finset.univ : Finset (Fin n)) \ T).card := by
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let e := slotSplitVacuumComponentEquiv (Finset.subset_univ T) ext vac hext
    let F : ↥(vacuumComponentParts d.vertexGraph) → ℕ := fun B =>
      (interactionSector
        (B.1 : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))).card
    change Fintype.card (d.MixedVacuumPair τ τ' σ) = _
    rw [← Fintype.card_congr (d.mixedVacuumPairSigmaEquiv τ τ' σ),
      Fintype.card_sigma]
    simp_rw [d.card_mixedVacuumComponentPair τ τ' σ]
    rw [← Finset.mul_sum]
    apply congrArg (2 * ·)
    calc
      (∑ B : ↥(vacuumComponentParts d.vertexGraph), F B) =
          ∑ C : vac.vertexGraph.componentPartitionOn.parts, F (e C) :=
        (Equiv.sum_comp e F).symm
      _ = ∑ C : vac.vertexGraph.componentPartitionOn.parts,
          (C : Finset (Fin n)).card := by
        apply Fintype.sum_congr
        intro C
        change (interactionSector
          ((e C).1.1 : Finset (TwoPointVertex
            (Finset.univ : Finset (Fin n))))).card = _
        rw [slotSplitVacuumComponentEquiv_apply,
          interactionSector_slotSplitVacuumComponentPart]
      _ = ((Finset.univ : Finset (Fin n)) \ T).card := by
        rw [Finset.sum_coe_sort]
        exact vac.vertexGraph.componentPartitionOn.sum_card_parts
  have hbij : Function.Bijective emb :=
    (Fintype.bijective_iff_injective_and_card emb).2
      ⟨emb.injective, hsource.trans htarget.symm⟩
  exact hbij.2

/-- The fixed-order quartic vacuum normalized pairs are equivalent to all ambient mixed normalized
pairs carried by vacuum components. -/
noncomputable def TwoPointDiagram.slotSplitVacuumMixedPairEquiv
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair ≃
      (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ :=
  Equiv.ofBijective (TwoPointDiagram.slotSplitVacuumMixedPairEmbedding T ext vac τ τ' σ hσ)
    ⟨(TwoPointDiagram.slotSplitVacuumMixedPairEmbedding T ext vac τ τ' σ hσ).injective,
      TwoPointDiagram.slotSplitVacuumMixedPairEmbedding_surjective
        T ext vac hext τ τ' σ hσ⟩

@[simp]
theorem TwoPointDiagram.slotSplitVacuumMixedPairEquiv_apply
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    (TwoPointDiagram.slotSplitVacuumMixedPairEquiv T ext vac hext τ τ' σ hσ pr).1 =
      TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ pr :=
  rfl

end Common
end SecondQuantization
