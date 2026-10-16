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

/-- The vacuum fixed-order leg embedding in mixed positions agrees with the
right-side leg of the canonical diagram slot split after returning to fixed positions. -/
private theorem slotSplitVacuumMixedPosition_eq_slotSplitRight
    (T : Finset (Fin n)) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    mixedTimeAmbientPositionEquiv τ τ' σ
        (mixedTimeOrderedQuarticLegMapPosition (slotSplitVacuumSlot T) τ τ' σ p) =
      slotLegSplitting (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg
          ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) p)) := by
  apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
  rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  change mixedTimeOrderedAtomicLegEquiv τ τ' σ
      (mixedTimeOrderedAtomicLegPosition τ τ' σ
        (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p)) = _
  rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  simpa only [Equiv.apply_symm_apply] using
    congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
      (slotSplitVacuumOrderedLeg_eq_slotSplitRight T p)

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
        slotLegSplitting (Finset.subset_univ T) (Sum.inr q) :=
    slotSplitVacuumMixedPosition_eq_slotSplitRight T τ τ' σ p
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

/-- A mixed pair in a vacuum component starts on the quartic side of the
reassembled slot split. This is the transport of the time-independent
vacuum-leg classification into mixed-time coordinates. -/
private theorem TwoPointDiagram.mixedVacuumPair_firstEndpoint_mem_vacuumLegRange
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ) :
    ∃ p, mixedTimeOrderedQuarticLegMapPosition
      (slotSplitVacuumSlot T) τ τ' σ p = pr.1.1.1 := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let i := mixedTimeAmbientPositionEquiv τ τ' σ pr.1.1.1
  have hVac : ComponentIsVacuum
      (d.vertexGraph.componentBlock (twoPointVertexOfLeg i)) :=
    (mem_vacuumComponentParts d.vertexGraph
      (d.mixedPairComponent τ τ' σ pr.1)).1 pr.2
  obtain ⟨q, hq⟩ :=
    TwoPointDiagram.ofSlotSplit_vacuumLeg_mem_right
      (Finset.subset_univ T) ext vac hext i hVac
  let p := (orderedLegToDiagramLeg
    ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T)).symm q
  refine ⟨p, ?_⟩
  apply (mixedTimeAmbientPositionEquiv τ τ' σ).injective
  rw [slotSplitVacuumMixedPosition_eq_slotSplitRight]
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
  refine Equiv.ofBijective
    (TwoPointDiagram.slotSplitVacuumMixedPairEmbedding T ext vac τ τ' σ hσ)
    ⟨(TwoPointDiagram.slotSplitVacuumMixedPairEmbedding T ext vac τ τ' σ hσ).injective,
      ?_⟩
  intro pr
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
      (TwoPointDiagram.mixedVacuumPair_firstEndpoint_mem_vacuumLegRange
        T ext vac hext τ τ' σ pr)
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
