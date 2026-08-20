import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumComponents

set_option linter.style.header false

/-!
# Image of the slot-split vacuum pair embedding

The fixed-order normalized pairs of a quartic vacuum piece embed into the mixed pairing of the
reassembled two-point diagram. This module identifies their image with exactly the ambient mixed
pairs carried by vacuum components and packages the resulting equivalence.

The construction is purely combinatorial and is stated for arbitrary external/internal labels.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {n : ℕ}

/-- Normalized mixed-time pairs whose full ambient component is a vacuum component. -/
abbrev TwoPointDiagram.MixedVacuumPair
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :=
  {pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair //
    d.mixedPairComponent τ τ' σ pr ∈ d.vacuumComponentParts}

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
      ⟨d.componentBlock (slotSplitVacuumVertex (vertexOfLeg q)),
        d.componentBlock_mem_componentPartition (slotSplitVacuumVertex (vertexOfLeg q))⟩ := by
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
    calc
      orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p =
          (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
            ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
              (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p)) := by
        rw [Equiv.apply_symm_apply]
      _ = (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
          (slotLegSplitting (Finset.subset_univ T) (Sum.inr q)) := by
        exact congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
          (by simpa [q] using slotSplitVacuumOrderedLeg_eq_slotSplitRight T p)
  have hvertex :
      twoPointVertexOfLeg
          (mixedTimeAmbientPositionEquiv τ τ' σ
            (mixedTimeOrderedQuarticLegMapPosition
              (slotSplitVacuumSlot T) τ τ' σ p)) =
        slotSplitVacuumVertex (vertexOfLeg q) := by
    rw [hleg, twoPointVertexOfLeg_slotLegSplitting_inr_exact]
  apply Subtype.ext
  change d.componentBlock
      (twoPointVertexOfLeg
        (mixedTimeAmbientPositionEquiv τ τ' σ
          (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
            T ext vac τ τ' σ hσ pr).1.1)) = _
  rw [TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_apply]
  exact congrArg d.componentBlock hvertex

/-- Every normalized pair from the standalone quartic vacuum piece belongs to an ambient vacuum
component after reassembly. -/
theorem TwoPointDiagram.ofSlotSplitVacuumNormalizedPairEmbedding_mem_vacuumComponentParts
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    d.mixedPairComponent τ τ' σ
        (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
          T ext vac τ τ' σ hσ pr) ∈ d.vacuumComponentParts := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let q := orderedLegToDiagramLeg
    ((Finset.univ : Finset (Fin n)) \ T) (slotSplitVacuumOrder T) pr.1.1
  change d.mixedPairComponent τ τ' σ
      (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
        T ext vac τ τ' σ hσ pr) ∈ d.vacuumComponentParts
  rw [TwoPointDiagram.ofSlotSplitVacuumNormalizedPairEmbedding_component
    T ext vac τ τ' σ hσ pr]
  exact componentBlock_slotSplitVacuumVertex_mem_vacuumComponentParts
    (Finset.subset_univ T) ext vac (vertexOfLeg q)

/-- The quartic normalized-pair embedding with codomain restricted to ambient vacuum-component
pairs. -/
noncomputable def TwoPointDiagram.slotSplitVacuumMixedPairEmbedding
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair ↪
      (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair τ τ' σ where
  toFun pr :=
    ⟨TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ pr,
      TwoPointDiagram.ofSlotSplitVacuumNormalizedPairEmbedding_mem_vacuumComponentParts
        T ext vac τ τ' σ hσ pr⟩
  inj' := by
    intro p q hpq
    apply (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ).injective
    exact congrArg Subtype.val hpq

@[simp]
theorem TwoPointDiagram.slotSplitVacuumMixedPairEmbedding_apply
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    (TwoPointDiagram.slotSplitVacuumMixedPairEmbedding
      T ext vac τ τ' σ hσ pr).1 =
      TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ pr :=
  rfl

/-- Ambient mixed vacuum pairs are the dependent disjoint union of the mixed pair fibers of the
ambient vacuum components. -/
noncomputable def TwoPointDiagram.mixedVacuumPairSigmaEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (Σ B : ↥d.vacuumComponentParts, d.MixedComponentPair τ τ' σ B.1) ≃
      d.MixedVacuumPair τ τ' σ where
  toFun x :=
    ⟨x.2.1, by
      rw [x.2.2]
      exact x.1.2⟩
  invFun pr :=
    ⟨⟨d.mixedPairComponent τ τ' σ pr.1, pr.2⟩, ⟨pr.1, rfl⟩⟩
  left_inv := by
    rintro ⟨B, pr⟩
    let B' : ↥d.vacuumComponentParts :=
      ⟨d.mixedPairComponent τ τ' σ pr.1, by
        rw [pr.2]
        exact B.2⟩
    have hB : B' = B := by
      apply Subtype.ext
      exact pr.2
    apply Sigma.ext hB
    refine (Subtype.heq_iff_coe_eq ?_).2 ?_
    · intro x
      change d.mixedPairComponent τ τ' σ x = B'.1 ↔
        d.mixedPairComponent τ τ' σ x = B.1
      rw [hB]
    · rfl
  right_inv _ := rfl

/-- One ambient vacuum-component mixed pair fiber has twice as many elements as interaction vertices
in that component. -/
theorem TwoPointDiagram.card_mixedVacuumComponentPair
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : ↥d.vacuumComponentParts) :
    Fintype.card (d.MixedComponentPair τ τ' σ B.1) =
      2 * (TwoPointDiagram.interactionPart
        (B.1 : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))).card := by
  let hVac : d.ComponentIsVacuum B.1 :=
    (d.mem_vacuumComponentParts B.1).1 B.2
  rw [Fintype.card_congr (d.mixedVacuumComponentPairEquiv τ τ' σ B.1 hVac)]
  simpa using (d.restrictedVacuumPairing B.1 hVac).card_normalizedPair

/-- For an externally connected left piece, the ambient vacuum components contain exactly the
interaction vertices of the standalone quartic right piece. -/
theorem TwoPointDiagram.ofSlotSplit_sum_vacuumComponentInteractionCard
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected) :
    let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    (∑ B : ↥d.vacuumComponentParts,
      (TwoPointDiagram.interactionPart
        (B.1 : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))).card) =
      ((Finset.univ : Finset (Fin n)) \ T).card := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let e := slotSplitVacuumComponentEquiv
    (Finset.subset_univ T) ext vac hext
  let F : ↥d.vacuumComponentParts → ℕ := fun B =>
    (TwoPointDiagram.interactionPart
      (B.1 : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))).card
  change (∑ B : ↥d.vacuumComponentParts, F B) = _
  calc
    (∑ B : ↥d.vacuumComponentParts, F B) =
        ∑ C : vac.componentPartition.parts, F (e C) :=
      (Equiv.sum_comp e F).symm
    _ = ∑ C : vac.componentPartition.parts, (C : Finset (Fin n)).card := by
      apply Fintype.sum_congr
      intro C
      change (TwoPointDiagram.interactionPart
          ((e C).1.1 : Finset (TwoPointVertex
            (Finset.univ : Finset (Fin n))))).card = _
      rw [slotSplitVacuumComponentEquiv_apply,
        interactionPart_slotSplitVacuumComponentPart]
    _ = ((Finset.univ : Finset (Fin n)) \ T).card := by
      rw [Finset.sum_coe_sort]
      exact vac.componentPartition.sum_card_parts

/-- The type of all ambient mixed vacuum pairs has the same cardinality as the normalized pairs of
the standalone quartic vacuum pairing. -/
theorem TwoPointDiagram.ofSlotSplit_card_mixedVacuumPair
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fintype.card ((TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedVacuumPair
      τ τ' σ) = 2 * ((Finset.univ : Finset (Fin n)) \ T).card := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  rw [← Fintype.card_congr (d.mixedVacuumPairSigmaEquiv τ τ' σ), Fintype.card_sigma]
  simp_rw [d.card_mixedVacuumComponentPair τ τ' σ]
  rw [← Finset.mul_sum]
  exact congrArg (2 * ·)
    (TwoPointDiagram.ofSlotSplit_sum_vacuumComponentInteractionCard T ext vac hext)

/-- Under external connectedness, every ambient mixed pair lying in a vacuum component comes from a
unique normalized pair of the standalone quartic vacuum pairing. -/
theorem TwoPointDiagram.slotSplitVacuumMixedPairEmbedding_surjective
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
        2 * ((Finset.univ : Finset (Fin n)) \ T).card :=
    TwoPointDiagram.ofSlotSplit_card_mixedVacuumPair T ext vac hext τ τ' σ
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
