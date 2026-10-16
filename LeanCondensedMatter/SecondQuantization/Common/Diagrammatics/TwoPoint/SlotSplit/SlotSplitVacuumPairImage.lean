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

The graph-level exclusion of external-side legs is proved without any time-order hypothesis
in `TwoPoint.SlotSplit.SlotSplitVacuumComponents`. The mixed-time coordinate identification
is local to this image comparison; `StrictAnti` is needed only for ordered pair endpoints.

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
    simpa only [mixedTimeOrderedQuarticLegMapPosition,
      mixedTimeAmbientPositionEquiv_mixedTimeOrderedAtomicLegPosition] using
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

/-- A mixed-time atomic position lies in a vacuum component of the assembled diagram
exactly when it comes from a quartic leg on the right of the slot split.
This does not depend on pair normalization or a time-order hypothesis. -/
theorem TwoPointDiagram.ofSlotSplit_vacuumMixedPosition_mem_range_iff
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (i : Fin (2 * (2 * n + 1))) :
    i ∈ Set.range (mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ) ↔
      ComponentIsVacuum
        ((TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).vertexGraph.componentBlock
          (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ i))) := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  constructor
  · rintro ⟨p, rfl⟩
    let q := orderedLegToDiagramLeg
      ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) p
    have hpos :
        mixedTimeAmbientPositionEquiv τ τ' σ
            (mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ p) =
          slotLegSplitting (Finset.subset_univ T) (Sum.inr q) := by
      simpa only [mixedTimeOrderedQuarticLegMapPosition,
        mixedTimeAmbientPositionEquiv_mixedTimeOrderedAtomicLegPosition] using
        (slotSplitVacuumOrderedLeg_eq_slotSplitRight T p)
    change ComponentIsVacuum (d.vertexGraph.componentBlock
      (twoPointVertexOfLeg
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ p))))
    rw [hpos, twoPointVertexOfLeg_slotLegSplitting_inr_exact]
    exact (mem_vacuumComponentParts d.vertexGraph _).1
      (componentBlock_slotSplitVacuumVertex_mem_vacuumComponentParts
        (Finset.subset_univ T) ext vac (vertexOfLeg q))
  · intro hVac
    obtain ⟨q, hq⟩ :=
      TwoPointDiagram.ofSlotSplit_vacuumLeg_mem_right
        (Finset.subset_univ T) ext vac hext
        (mixedTimeAmbientPositionEquiv τ τ' σ i) hVac
    let p := (orderedLegToDiagramLeg
      ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T)).symm q
    refine ⟨p, ?_⟩
    apply (mixedTimeAmbientPositionEquiv τ τ' σ).injective
    simp only [mixedTimeOrderedQuarticLegMapPosition,
      mixedTimeAmbientPositionEquiv_mixedTimeOrderedAtomicLegPosition,
      slotSplitVacuumOrderedLeg_eq_slotSplitRight]
    simpa only [p, Equiv.apply_symm_apply] using hq

/-- The fixed-order quartic vacuum normalized pairs are equivalent to all ambient mixed normalized
pairs carried by vacuum components. The graph-to-mixed-position characterization is kept
separate; the one-use surjectivity proof is constructed directly here. -/
noncomputable def TwoPointDiagram.slotSplitVacuumMixedPairEquiv
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair ≃
      (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ :=
by
  let embed :
      (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair →
        (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ :=
    fun pr =>
      ⟨TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ pr,
        by
          rw [TwoPointDiagram.ofSlotSplitVacuumNormalizedPairEmbedding_component
            T ext vac τ τ' σ hσ pr]
          exact componentBlock_slotSplitVacuumVertex_mem_vacuumComponentParts
            (Finset.subset_univ T) ext vac
            (vertexOfLeg (orderedLegToDiagramLeg
              ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) pr.1.1))⟩
  refine Equiv.ofBijective embed ⟨?_, ?_⟩
  · intro p q hpq
    apply (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ).injective
    exact congrArg Subtype.val hpq
  · intro pr
    obtain ⟨q, hq⟩ : ∃ q,
        TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ q =
          pr.1 := by
      let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
      let e := mixedTimeOrderedQuarticLegMapOrderEmbedding
        (slotSplitVacuumSlot T) (slotSplitVacuumSlot_strictMono T) τ τ' σ hσ
      have hpartner (i) :
          (d.pairingInMixedOrder τ τ' σ).partner (e i) =
            e ((vac.pairingInOrder (slotSplitVacuumOrder T)).partner i) := by
        change (d.pairingInMixedOrder τ τ' σ).partner
            (mixedTimeOrderedAtomicLegPosition τ τ' σ
              (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) i)) = _
        rw [d.pairingInMixedOrder_partner_legPosition]
        apply congrArg (mixedTimeOrderedAtomicLegPosition τ τ' σ)
        apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm.injective
        rw [TwoPointDiagram.atomicLegPartner, Equiv.symm_apply_apply]
        exact TwoPointDiagram.ofSlotSplit_pairing_partner_vacuumOrderedLeg
          T ext vac i
      exact Pairing.exists_normalizedPairEmbedding_eq_of_firstEndpoint
        (vac.pairingInOrder (slotSplitVacuumOrder T))
        (d.pairingInMixedOrder τ τ' σ) e hpartner pr.1
        ((TwoPointDiagram.ofSlotSplit_vacuumMixedPosition_mem_range_iff
          T ext vac hext τ τ' σ pr.1.1.1).2
          ((mem_vacuumComponentParts d.vertexGraph
            (d.mixedPairComponent τ τ' σ pr.1)).1 pr.2))
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact hq

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
