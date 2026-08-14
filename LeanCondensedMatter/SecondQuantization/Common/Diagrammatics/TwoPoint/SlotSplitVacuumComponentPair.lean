import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumPairComponent
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.FixedOrderComponentPair

set_option linter.style.header false

/-!
# Componentwise slot-split vacuum pair equivalence

The normalized pairs of one restricted quartic vacuum component embed into exactly the mixed pair
fiber of the corresponding ambient vacuum component after reassembly. Equal finite cardinalities
upgrade the embedding to an equivalence, and its monotone endpoint embedding preserves crossing
geometry and component-internal crossing counts.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {n : ℕ}

/-- Embed one restricted quartic component's normalized pairs into the corresponding ambient mixed
vacuum-component pair fiber. -/
noncomputable def TwoPointDiagram.slotSplitVacuumComponentPairEmbedding
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    vac.LocalOrderedPair (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)) C ↪
      (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedComponentPair τ τ' σ
        (slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac C).1 where
  toFun pr := by
    let globalPr := vac.fixedOrderComponentPairEmbedding (slotSplitVacuumOrder T) C pr
    let ambientPr := TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ globalPr
    refine ⟨ambientPr, ?_⟩
    rw [TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_pairComponent
      T ext vac τ τ' σ hσ globalPr,
      vac.fixedOrderPairComponent_fixedOrderComponentPairEmbedding]
  inj' := by
    intro p q hpq
    apply (vac.fixedOrderComponentPairEmbedding (slotSplitVacuumOrder T) C).injective
    apply (TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ).injective
    exact congrArg Subtype.val hpq

/-- Source and target of the componentwise vacuum-pair embedding have equal finite cardinality. -/
theorem TwoPointDiagram.slotSplitVacuumComponentPairEmbedding_card_eq
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fintype.card
        (vac.LocalOrderedPair
          (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)) C) =
      Fintype.card
        ((TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedComponentPair τ τ' σ
          (slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac C).1) := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let B := slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac C
  calc
    Fintype.card
        (vac.LocalOrderedPair
          (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)) C) =
        2 * (C : Finset (Fin n)).card := by
      simpa using
        ((vac.restrictComponent C.2).pairingInOrder
          (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T) C)).card_normalizedPair
    _ = 2 * (TwoPointDiagram.interactionPart
        (B.1 : Finset (TwoPointVertex (Finset.univ : Finset (Fin n))))).card := by
      rw [interactionPart_slotSplitVacuumComponentPart]
    _ = Fintype.card (d.MixedComponentPair τ τ' σ B.1) := by
      symm
      exact d.card_mixedVacuumComponentPair τ τ' σ B

/-- One restricted quartic vacuum component's normalized pairs are equivalent to the corresponding
ambient mixed component-pair fiber. -/
noncomputable def TwoPointDiagram.slotSplitVacuumComponentPairEquiv
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    vac.LocalOrderedPair (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)) C ≃
      (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).MixedComponentPair τ τ' σ
        (slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac C).1 :=
  let emb := TwoPointDiagram.slotSplitVacuumComponentPairEmbedding T ext vac C τ τ' σ hσ
  Equiv.ofBijective emb
    ((Fintype.bijective_iff_injective_and_card emb).2
      ⟨emb.injective,
        TwoPointDiagram.slotSplitVacuumComponentPairEmbedding_card_eq
          T ext vac C τ τ' σ⟩)

@[simp]
theorem TwoPointDiagram.slotSplitVacuumComponentPairEquiv_apply
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : vac.LocalOrderedPair
      (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)) C) :
    (TwoPointDiagram.slotSplitVacuumComponentPairEquiv
      T ext vac C τ τ' σ hσ pr).1 =
      TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
        T ext vac τ τ' σ hσ
        (vac.fixedOrderComponentPairEmbedding (slotSplitVacuumOrder T) C pr) :=
  rfl

/-- The componentwise pair equivalence preserves and reflects crossing geometry. -/
theorem TwoPointDiagram.slotSplitVacuumComponentPairEquiv_crosses_iff
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (p q : vac.LocalOrderedPair
      (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)) C) :
    Crosses
        (TwoPointDiagram.slotSplitVacuumComponentPairEquiv
          T ext vac C τ τ' σ hσ p).1.1
        (TwoPointDiagram.slotSplitVacuumComponentPairEquiv
          T ext vac C τ τ' σ hσ q).1.1 ↔
      Crosses p.1 q.1 := by
  rw [TwoPointDiagram.slotSplitVacuumComponentPairEquiv_apply,
    TwoPointDiagram.slotSplitVacuumComponentPairEquiv_apply,
    TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding_crosses_iff,
    vac.fixedOrderComponentPairEmbedding_crosses_iff]

/-- Internal crossing counts agree componentwise between the standalone fixed-order quartic vacuum
pairing and the corresponding ambient mixed vacuum component. -/
theorem TwoPointDiagram.ofSlotSplit_mixedComponentCrossingCount_vacuum_eq
    (T : Finset (Fin n))
    (ext : TwoPointDiagram ExternalLabel InternalLabel n T)
    (vac : QuarticDiagram InternalLabel n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    (TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).mixedComponentCrossingCount τ τ' σ
        (slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac C).1 =
      ((vac.restrictComponent C.2).pairingInOrder
        (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T) C)).crossingCount := by
  let d := TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
  let B : d.componentPartition.parts :=
    (slotSplitVacuumComponentPart (Finset.subset_univ T) ext vac C).1
  let LocalPair := vac.LocalOrderedPair
    (vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)) C
  let AmbientPair := d.MixedComponentPair τ τ' σ B
  let e : LocalPair ≃ AmbientPair :=
    TwoPointDiagram.slotSplitVacuumComponentPairEquiv T ext vac C τ τ' σ hσ
  rw [TwoPointDiagram.mixedComponentCrossingCount,
    TwoPointDiagram.mixedComponentOrientedCrossingCount,
    Pairing.componentCrossingCount, Fintype.sum_prod_type,
    Pairing.crossingCount_eq_sum_sum_crosses]
  simp only [TwoPointDiagram.mixedComponentPairSigmaEquiv_apply]
  symm
  refine Fintype.sum_equiv e
    (fun p : LocalPair => ∑ q : LocalPair, if Crosses p.1 q.1 then 1 else 0)
    (fun p' : AmbientPair => ∑ q' : AmbientPair, if Crosses p'.1.1 q'.1.1 then 1 else 0) ?_
  intro p
  refine Fintype.sum_equiv e
    (fun q : LocalPair => if Crosses p.1 q.1 then 1 else 0)
    (fun q' : AmbientPair => if Crosses (e p).1.1 q'.1.1 then 1 else 0) ?_
  intro q
  have hcross : Crosses (e p).1.1 (e q).1.1 ↔ Crosses p.1 q.1 :=
    TwoPointDiagram.slotSplitVacuumComponentPairEquiv_crosses_iff
      T ext vac C τ τ' σ hσ p q
  by_cases h : Crosses p.1 q.1
  · rw [if_pos h, if_pos (hcross.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hcross.mp h'))]

end Common
end SecondQuantization
