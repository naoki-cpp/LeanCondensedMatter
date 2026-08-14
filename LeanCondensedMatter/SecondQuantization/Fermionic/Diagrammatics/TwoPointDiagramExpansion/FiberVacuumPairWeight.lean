import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPairComponent
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentOrderDecomposition

set_option linter.style.header false

/-!
# Pairing weight on the vacuum half of a fixed external-slot fiber

For one connected component of the standalone quartic vacuum piece, its canonical fixed-order local
pairs embed into the full fixed-order vacuum pairing and then into the ambient mixed two-point
pairing.  The component index is preserved by `FiberVacuumPairComponent`; equal finite cardinalities
upgrade this map to a componentwise equivalence.  Crossing covariance then identifies the internal
crossing count of each ambient vacuum component with the crossing count of the corresponding
restricted quartic component.

Reindexing the component product and using the existing quartic component parity theorem gives the
complete fermionic exchange weight of the standalone fixed-order vacuum pairing.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} {n : ℕ} {i j : Mode}

/-- The canonical component shuffle induced by one fixed quartic vertex order. -/
noncomputable def QuarticWickDiagram.fixedOrderComponentShuffle
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) : d.ComponentShuffle :=
  d.shuffleOfVertexOrder order (d.componentVertexOrdersOfVertexOrder order)
    (d.componentOrdersCompatible_componentVertexOrdersOfVertexOrder order)

@[simp]
theorem QuarticWickDiagram.assembleVertexOrder_fixedOrderComponentShuffle
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    d.assembleVertexOrder (d.componentVertexOrdersOfVertexOrder order)
        (d.fixedOrderComponentShuffle order) = order :=
  d.assembleVertexOrder_shuffleOfVertexOrder order
    (d.componentVertexOrdersOfVertexOrder order)
    (d.componentOrdersCompatible_componentVertexOrdersOfVertexOrder order)

/-- Embed the normalized pairs of one restricted component into the normalized pairs of the global
pairing in the fixed vertex order. -/
noncomputable def QuarticWickDiagram.fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) (C : d.componentPartition.parts) :
    d.LocalOrderedPair (d.componentVertexOrdersOfVertexOrder order) C ↪
      (d.pairingInOrder order).NormalizedPair where
  toFun pr := by
    let shuffle := d.fixedOrderComponentShuffle order
    have hmem :
        (d.componentOrderedLeg shuffle C pr.1.1,
          d.componentOrderedLeg shuffle C pr.1.2) ∈
          (d.pairingInOrder
            (d.assembleVertexOrder (d.componentVertexOrdersOfVertexOrder order) shuffle)).pairs :=
      (d.mem_pairingInOrder_pairs_componentOrderedLeg_iff
        (d.componentVertexOrdersOfVertexOrder order) shuffle C pr.1.1 pr.1.2).2 pr.2
    rw [d.assembleVertexOrder_fixedOrderComponentShuffle order] at hmem
    exact ⟨(d.componentOrderedLeg shuffle C pr.1.1,
      d.componentOrderedLeg shuffle C pr.1.2), hmem⟩
  inj' := by
    intro p q hpq
    let shuffle := d.fixedOrderComponentShuffle order
    have hinj := (d.componentOrderedLeg_strictMono shuffle C).injective
    apply Subtype.ext
    apply Prod.ext
    · apply hinj
      exact congrArg (fun z => z.1.1) hpq
    · apply hinj
      exact congrArg (fun z => z.1.2) hpq

@[simp]
theorem QuarticWickDiagram.fixedOrderComponentPairEmbedding_apply
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) (C : d.componentPartition.parts)
    (pr : d.LocalOrderedPair (d.componentVertexOrdersOfVertexOrder order) C) :
    (d.fixedOrderComponentPairEmbedding order C pr).1 =
      (d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.1,
        d.componentOrderedLeg (d.fixedOrderComponentShuffle order) C pr.1.2) :=
  rfl

/-- The fixed-order component-pair embedding preserves and reflects crossings. -/
theorem QuarticWickDiagram.fixedOrderComponentPairEmbedding_crosses_iff
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) (C : d.componentPartition.parts)
    (p q : d.LocalOrderedPair (d.componentVertexOrdersOfVertexOrder order) C) :
    Crosses (d.fixedOrderComponentPairEmbedding order C p).1
        (d.fixedOrderComponentPairEmbedding order C q).1 ↔
      Crosses p.1 q.1 := by
  rw [d.fixedOrderComponentPairEmbedding_apply,
    d.fixedOrderComponentPairEmbedding_apply]
  exact crosses_map_iff
    (d.componentOrderedLegOrderEmbedding (d.fixedOrderComponentShuffle order) C)
    (d.componentOrderedLegOrderEmbedding (d.fixedOrderComponentShuffle order) C).strictMono
    p.1.1 p.1.2 q.1.1 q.1.2

/-- A component-local normalized pair remains assigned to that component after embedding into the
fixed global quartic order. -/
theorem QuarticWickDiagram.fixedOrderPairComponent_fixedOrderComponentPairEmbedding
    {N : ℕ} {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) (C : d.componentPartition.parts)
    (pr : d.LocalOrderedPair (d.componentVertexOrdersOfVertexOrder order) C) :
    d.fixedOrderPairComponent order (d.fixedOrderComponentPairEmbedding order C pr) = C := by
  apply Subtype.ext
  apply (d.componentBlock_eq_iff_mem C.2 _).2
  let shuffle := d.fixedOrderComponentShuffle order
  let localLeg := Common.orderedLegToDiagramLeg (C : Finset (Fin N))
    (d.componentVertexOrdersOfVertexOrder order C) pr.1.1
  have hleg := d.orderedLegToDiagramLeg_componentOrderedLeg
    (d.componentVertexOrdersOfVertexOrder order) shuffle C pr.1.1
  rw [d.assembleVertexOrder_fixedOrderComponentShuffle order] at hleg
  change ((Common.vertexOfLeg
      (Common.orderedLegToDiagramLeg S order
        (d.fixedOrderComponentPairEmbedding order C pr).1.1) : ↥S) : Fin N) ∈
    (C : Finset (Fin N))
  rw [d.fixedOrderComponentPairEmbedding_apply, hleg]
  have hv := d.vertexOfLeg_componentDiagramLeg_val C localLeg
  rw [hv]
  exact (Common.vertexOfLeg localLeg).2

/-- Embed one restricted quartic component's normalized pairs into the corresponding ambient mixed
vacuum-component pair fiber. -/
noncomputable def fixedExternalOfSlotSplitVacuumComponentPairEmbedding
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T)) :
    vac.LocalOrderedPair (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)) C ↪
      (fixedExternalOfSlotSplit T ext vac).1.MixedComponentPair τ τ' σ
        (Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac C).1 where
  toFun pr := by
    let globalPr := vac.fixedOrderComponentPairEmbedding (fixedExternalVacuumOrder T) C pr
    let ambientPr := fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ globalPr
    refine ⟨ambientPr, ?_⟩
    rw [fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding_pairComponent
      T ext vac τ τ' σ hσ globalPr,
      vac.fixedOrderPairComponent_fixedOrderComponentPairEmbedding]
  inj' := by
    intro p q hpq
    apply (vac.fixedOrderComponentPairEmbedding (fixedExternalVacuumOrder T) C).injective
    apply (fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ).injective
    exact congrArg Subtype.val hpq

/-- Source and target of the componentwise vacuum-pair embedding have equal finite cardinality. -/
theorem fixedExternalOfSlotSplitVacuumComponentPairEmbedding_card_eq
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fintype.card
        (vac.LocalOrderedPair
          (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)) C) =
      Fintype.card
        ((fixedExternalOfSlotSplit T ext vac).1.MixedComponentPair τ τ' σ
          (Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac C).1) := by
  let d := fixedExternalOfSlotSplit T ext vac
  let B := Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac C
  calc
    Fintype.card
        (vac.LocalOrderedPair
          (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)) C) =
        2 * (C : Finset (Fin n)).card := by
      simpa using
        ((vac.restrictComponent C.2).pairingInOrder
          (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T) C)).card_normalizedPair
    _ = 2 * (Common.TwoPointDiagram.interactionPart
        (B.1 : Finset (Common.TwoPointVertex (Finset.univ : Finset (Fin n))))).card := by
      rw [Common.interactionPart_slotSplitVacuumComponentPart]
    _ = Fintype.card (d.1.MixedComponentPair τ τ' σ B.1) := by
      symm
      exact d.card_mixedVacuumComponentPair τ τ' σ B

/-- One restricted quartic vacuum component's normalized pairs are equivalent to the corresponding
ambient mixed component-pair fiber. -/
noncomputable def fixedExternalOfSlotSplitVacuumComponentPairEquiv
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T)) :
    vac.LocalOrderedPair (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)) C ≃
      (fixedExternalOfSlotSplit T ext vac).1.MixedComponentPair τ τ' σ
        (Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac C).1 :=
  let emb := fixedExternalOfSlotSplitVacuumComponentPairEmbedding T ext vac C τ τ' σ hσ
  Equiv.ofBijective emb
    ((Fintype.bijective_iff_injective_and_card emb).2
      ⟨emb.injective,
        fixedExternalOfSlotSplitVacuumComponentPairEmbedding_card_eq
          T ext vac C τ τ' σ⟩)

@[simp]
theorem fixedExternalOfSlotSplitVacuumComponentPairEquiv_apply
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T))
    (pr : vac.LocalOrderedPair
      (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)) C) :
    (fixedExternalOfSlotSplitVacuumComponentPairEquiv
      T ext vac C τ τ' σ hσ pr).1 =
      fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding T ext vac τ τ' σ hσ
        (vac.fixedOrderComponentPairEmbedding (fixedExternalVacuumOrder T) C pr) :=
  rfl

/-- The componentwise pair equivalence preserves and reflects crossing geometry. -/
theorem fixedExternalOfSlotSplitVacuumComponentPairEquiv_crosses_iff
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T))
    (p q : vac.LocalOrderedPair
      (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)) C) :
    Crosses
        (fixedExternalOfSlotSplitVacuumComponentPairEquiv
          T ext vac C τ τ' σ hσ p).1.1
        (fixedExternalOfSlotSplitVacuumComponentPairEquiv
          T ext vac C τ τ' σ hσ q).1.1 ↔
      Crosses p.1 q.1 := by
  rw [fixedExternalOfSlotSplitVacuumComponentPairEquiv_apply,
    fixedExternalOfSlotSplitVacuumComponentPairEquiv_apply,
    fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding_crosses_iff,
    vac.fixedOrderComponentPairEmbedding_crosses_iff]

/-- Internal crossing counts agree componentwise between the standalone fixed-order quartic vacuum
pairing and the corresponding ambient mixed vacuum component. -/
theorem fixedExternalOfSlotSplit_mixedComponentCrossingCount_vacuum_eq
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (C : vac.componentPartition.parts)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T)) :
    (fixedExternalOfSlotSplit T ext vac).1.mixedComponentCrossingCount τ τ' σ
        (Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac C).1 =
      ((vac.restrictComponent C.2).pairingInOrder
        (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T) C)).crossingCount := by
  let B : (fixedExternalOfSlotSplit T ext vac).1.componentPartition.parts :=
    (Common.slotSplitVacuumComponentPart (Finset.subset_univ T) ext.1 vac C).1
  let LocalPair := vac.LocalOrderedPair
    (vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)) C
  let AmbientPair := (fixedExternalOfSlotSplit T ext vac).1.MixedComponentPair τ τ' σ B
  let e : LocalPair ≃ AmbientPair :=
    fixedExternalOfSlotSplitVacuumComponentPairEquiv T ext vac C τ τ' σ hσ
  rw [Common.TwoPointDiagram.mixedComponentCrossingCount,
    Common.TwoPointDiagram.mixedComponentOrientedCrossingCount,
    Pairing.componentCrossingCount, Fintype.sum_prod_type,
    Pairing.crossingCount_eq_sum_sum_crosses]
  simp only [Common.TwoPointDiagram.mixedComponentPairSigmaEquiv_apply]
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
    fixedExternalOfSlotSplitVacuumComponentPairEquiv_crosses_iff
      T ext vac C τ τ' σ hσ p q
  by_cases h : Crosses p.1 q.1
  · rw [if_pos h, if_pos (hcross.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hcross.mp h'))]

/-- The product of all ambient vacuum-component fermionic weights is the weight of the standalone
fixed-order quartic vacuum pairing. -/
theorem fixedExternalOfSlotSplit_prod_vacuumMixedComponentWeight_eq
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.1.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.1.vacuumComponentParts.prod
        (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ) =
      (vac.pairingInOrder (fixedExternalVacuumOrder T)).weight Common.Statistics.fermion := by
  change (Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac).vacuumComponentParts.prod
      ((fixedExternalOfSlotSplit T ext vac).1.mixedComponentWeight
        Common.Statistics.fermion τ τ' σ) = _
  let e := Common.slotSplitVacuumComponentEquiv
    (Finset.subset_univ T) ext.1 vac hext
  let orders := vac.componentVertexOrdersOfVertexOrder (fixedExternalVacuumOrder T)
  let shuffle := vac.fixedOrderComponentShuffle (fixedExternalVacuumOrder T)
  calc
    (Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac).vacuumComponentParts.prod
        ((fixedExternalOfSlotSplit T ext vac).1.mixedComponentWeight
          Common.Statistics.fermion τ τ' σ) =
      ∏ B : ↥(Common.TwoPointDiagram.ofSlotSplit
          (Finset.subset_univ T) ext.1 vac).vacuumComponentParts,
        (fixedExternalOfSlotSplit T ext vac).1.mixedComponentWeight
          Common.Statistics.fermion τ τ' σ B.1 := by
      exact Finset.prod_subtype
        (Common.TwoPointDiagram.ofSlotSplit
          (Finset.subset_univ T) ext.1 vac).vacuumComponentParts
        (fun _ => Iff.rfl) _
    _ = ∏ C : vac.componentPartition.parts,
        (fixedExternalOfSlotSplit T ext vac).1.mixedComponentWeight
          Common.Statistics.fermion τ τ' σ (e C).1 :=
      (Equiv.prod_comp e (fun B =>
        (fixedExternalOfSlotSplit T ext vac).1.mixedComponentWeight
          Common.Statistics.fermion τ τ' σ B.1)).symm
    _ = ∏ C : vac.componentPartition.parts,
        ((vac.restrictComponent C.2).pairingInOrder (orders C)).weight
          Common.Statistics.fermion := by
      apply Fintype.prod_congr
      intro C
      rw [Common.slotSplitVacuumComponentEquiv_apply]
      have hcross := fixedExternalOfSlotSplit_mixedComponentCrossingCount_vacuum_eq
        T ext vac C τ τ' σ hσ
      simpa [Common.TwoPointDiagram.mixedComponentWeight, orders] using
        congrArg (fun k : ℕ => (-1 : ℂ) ^ k) hcross
    _ = (vac.pairingInOrder (vac.assembleVertexOrder orders shuffle)).weight
        Common.Statistics.fermion :=
      (vac.pairingInOrder_weight_eq_prod_components
        Common.Statistics.fermion orders shuffle).symm
    _ = (vac.pairingInOrder (fixedExternalVacuumOrder T)).weight
        Common.Statistics.fermion := by
      rw [vac.assembleVertexOrder_fixedOrderComponentShuffle]

end Fermionic
end SecondQuantization
