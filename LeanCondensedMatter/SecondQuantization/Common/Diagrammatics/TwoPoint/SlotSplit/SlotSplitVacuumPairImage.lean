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

/-- A mixed pair in an ambient vacuum component starts at a leg of the quartic
vacuum sector. The exclusion of left-sector legs uses external connectedness,
not a comparison of the numbers of pairing edges. -/
private theorem TwoPointDiagram.mixedVacuumPair_firstEndpoint_mem_vacuumLegRange
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ) :
    ∃ p, mixedTimeOrderedQuarticLegMapPosition
      (slotSplitVacuumSlot T) τ τ' σ p = pr.1.1.1 := by
  classical
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let i := mixedTimeAmbientPositionEquiv τ τ' σ pr.1.1.1
  let split := slotLegSplitting (Finset.subset_univ T)
  have hi : split (split.symm i) = i := split.apply_symm_apply i
  cases hside : split.symm i with
  | inl p =>
      have hleft : twoPointVertexOfLeg i ∈
          d.vertexGraph.componentBlock (Sum.inl 0) := by
        have hv :
            twoPointVertexOfLeg i =
              slotSplitVertex (Finset.subset_univ T) (twoPointVertexOfLeg p) := by
          rw [← hi, hside]
          exact twoPointVertexOfLeg_slotLegSplitting_inl (Finset.subset_univ T) p
        rw [hv]
        cases hvertex : twoPointVertexOfLeg p with
        | inl e =>
            change (Sum.inl e : TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
              d.vertexGraph.componentBlock (Sum.inl 0)
            exact d.externalVertex_mem_externalComponentPart e
        | inr v =>
            have hmem : (v : Fin n) ∈
                interactionSector (d.vertexGraph.componentBlock (Sum.inl 0)) := by
              rw [interactionSector_externalComponent_ofSlotSplit
                (Finset.subset_univ T) ext vac hext]
              exact v.2
            change (Sum.inr ⟨v.1, Finset.mem_univ _⟩ :
              TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
                d.vertexGraph.componentBlock (Sum.inl 0)
            exact (mem_interactionSector_subtype
              (d.vertexGraph.componentBlock (Sum.inl 0))
              ⟨v.1, Finset.mem_univ _⟩).1 hmem
      have hVac : ComponentIsVacuum
          (d.vertexGraph.componentBlock (twoPointVertexOfLeg i)) := by
        exact (mem_vacuumComponentParts d.vertexGraph
          (d.mixedPairComponent τ τ' σ pr.1)).1 pr.2
      have hblock : d.vertexGraph.componentBlock (twoPointVertexOfLeg i) =
          d.vertexGraph.componentBlock (Sum.inl 0) :=
        (d.vertexGraph.componentBlock_eq_iff_mem
          (d.vertexGraph.componentBlock_mem_componentPartition (Sum.inl 0))
          (twoPointVertexOfLeg i)).2 hleft
      have hzero : (Sum.inl (0 : Fin 2) :
          TwoPointVertex (Finset.univ : Finset (Fin n))) ∈
            d.vertexGraph.componentBlock (twoPointVertexOfLeg i) := by
        rw [hblock]
        exact d.vertexGraph.self_mem_componentBlock (Sum.inl 0)
      exact False.elim (hVac ⟨0, hzero⟩)
  | inr q =>
      let p := (orderedLegToDiagramLeg
        ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T)).symm q
      refine ⟨p, ?_⟩
      apply (mixedTimeAmbientPositionEquiv τ τ' σ).injective
      rw [slotSplitVacuumMixedPosition_eq_slotSplitRight]
      change split (Sum.inr ((orderedLegToDiagramLeg
        ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T)) p)) = i
      simpa only [p, Equiv.apply_symm_apply] using (by
        rw [hside] at hi
        exact hi)

/-- The restriction of a mixed vacuum-component pair to the complementary quartic
sector is surjective on normalized pairs, without counting their cardinalities. -/
private theorem TwoPointDiagram.slotSplitVacuumMixedPairEmbedding_surjective
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    Function.Surjective
      (TwoPointDiagram.slotSplitVacuumMixedPairEmbedding T ext vac τ τ' σ hσ) := by
  intro pr
  obtain ⟨q, hq⟩ :=
    TwoPointDiagram.exists_slotSplitVacuumNormalizedPairEmbedding_eq_of_firstEndpoint
      T ext vac τ τ' σ hσ pr.1
      (TwoPointDiagram.mixedVacuumPair_firstEndpoint_mem_vacuumLegRange
        T ext vac hext τ τ' σ pr)
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact hq

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
