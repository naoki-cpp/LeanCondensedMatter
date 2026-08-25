import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Factorization.FiberDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Factorization.MixedComponentDysonValue
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Amplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairImage
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumComponentPair
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.ComponentGlobalCrossingParity

set_option linter.style.header false

/-!
# Fixed-order contraction integrand on the vacuum half of a fixed external-slot fiber

The vacuum half of a reassembled two-point diagram is identified directly with the standalone
fixed-order quartic vacuum integrand. This file owns the whole fermionic transport chain: Dyson and
coupling prefactors, inherited vacuum fields/operators, pair contractions, component crossing
weights, and the final quartic integrand. Intermediate transport facts are proof-local; the public
endpoint is the complete vacuum-integrand identity consumed by the shuffle factorization.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
private theorem fixedExternalOfSlotSplit_prod_vacuumDysonSign_mul_vertexWeight
    (g : QuarticVertexLabel Mode → ℂ) (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (hext : ext.1.IsExternallyConnected)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.1.vacuumComponentParts.prod (fun B =>
      d.mixedComponentDysonSign B * d.mixedComponentVertexWeight g B) =
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g := by
  classical
  let d := fixedExternalOfSlotSplit T ext vac
  change d.1.vacuumComponentParts.prod (fun B =>
      d.mixedComponentDysonSign B * d.mixedComponentVertexWeight g B) = _
  rw [Finset.prod_mul_distrib]
  have hsign : d.1.vacuumComponentParts.prod d.mixedComponentDysonSign =
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card := by
    have hsignFn :
        d.mixedComponentDysonSign = fun B : d.1.componentPartition.parts =>
          (-1 : ℂ) ^ (Common.TwoPointDiagram.interactionPart
            (B.1 : Finset (Common.TwoPointVertex
              (Finset.univ : Finset (Fin n))))).card := by
      funext B
      rfl
    rw [hsignFn]
    simpa [d, fixedExternalOfSlotSplit] using
      (Common.TwoPointDiagram.prod_slotSplitVacuumComponentSigns_eq
        (Finset.subset_univ T) ext.1 vac hext)
  have hvertex : d.1.vacuumComponentParts.prod (d.mixedComponentVertexWeight g) =
      vac.couplingWeight g := by
    have hvertexFn :
        d.mixedComponentVertexWeight g = fun B : d.1.componentPartition.parts =>
          ∏ v : ↥(Common.TwoPointDiagram.interactionPart
            (B.1 : Finset (Common.TwoPointVertex
              (Finset.univ : Finset (Fin n))))),
            g (d.1.vertexLabel
              ⟨v.1, Common.TwoPointDiagram.interactionPart_subset
                (B.1 : Finset (Common.TwoPointVertex
                  (Finset.univ : Finset (Fin n)))) v.2⟩) := by
      funext B
      rfl
    rw [hvertexFn]
    simpa [d, fixedExternalOfSlotSplit,
      QuarticWickDiagram.couplingWeight, Common.QuarticDiagram.vertexWeight] using
      (Common.TwoPointDiagram.prod_slotSplitVacuumComponents_eq_vacuumVertexProduct
        (Finset.subset_univ T) ext.1 vac hext g)
  rw [hsign, hvertex]

omit [Fintype Mode] in
private theorem fixedExternalOfSlotSplit_mixedAtomicOperator_vacuumOrderedLeg
    (ε : Mode → ℝ)
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    mixedTimeOrderedAtomicOperatorFamily ε i j τ τ'
        (fixedExternalOfSlotSplit T ext vac).vertexLabelSequence σ
        (mixedTimeOrderedQuarticLegMapPosition
          (slotSplitVacuumSlot T) τ τ' σ p) =
      orderedQuarticLegOperator ε vac (slotSplitVacuumOrder T)
        (σ ∘ slotSplitVacuumSlot T) p := by
  rw [mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegField]
  change timedFieldOperator ε
      (orderedTwoPointLegField i j τ τ'
        (fixedExternalOfSlotSplit T ext vac).vertexLabelSequence σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ
          (mixedTimeOrderedAtomicLegPosition τ τ' σ
            (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p)))) = _
  rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]
  let q := Common.orderedQuarticLegEquiv
    ((Finset.univ : Finset (Fin n)) \ T).card p
  have hfield :
      orderedTwoPointLegField i j τ τ'
          (fixedExternalOfSlotSplit T ext vac).vertexLabelSequence σ
          (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p) =
        ⟨(σ ∘ slotSplitVacuumSlot T) q.1,
          quarticLocalLegExternalFieldLabel
            (vac.vertexLabel (slotSplitVacuumOrder T q.1)) q.2⟩ := by
    have hp :
        (Common.orderedQuarticLegEquiv
          ((Finset.univ : Finset (Fin n)) \ T).card).symm q = p :=
      (Common.orderedQuarticLegEquiv
        ((Finset.univ : Finset (Fin n)) \ T).card).symm_apply_apply p
    rw [← hp]
    rcases q with ⟨v, l⟩
    simp only [orderedQuarticLegMapToTwoPointLeg,
      orderedQuarticLegToTwoPointLeg_orderedQuarticLegEquiv_symm,
      orderedTwoPointLegMap_inr, orderedTwoPointLegField,
      orderedTwoPointLegTime, orderedTwoPointLegFieldLabel, Function.comp_apply]
    have hlabel :
        (fixedExternalOfSlotSplit T ext vac).vertexLabelSequence (slotSplitVacuumSlot T v) =
          vac.vertexLabel (slotSplitVacuumOrder T v) := by
      let w := slotSplitVacuumOrder T v
      have hwNot : (w.1 : Fin n) ∉ T := (Finset.mem_sdiff.mp w.2).2
      change (Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac).vertexLabel
          ⟨slotSplitVacuumSlot T v, Finset.mem_univ _⟩ = vac.vertexLabel w
      rw [Common.TwoPointDiagram.ofSlotSplit_vertexLabel_of_not_mem
        (Finset.subset_univ T) ext.1 vac _ (by simpa [slotSplitVacuumSlot, w] using hwNot)]
      apply congrArg vac.vertexLabel
      apply Subtype.ext
      rfl
    rw [hlabel]
  rw [hfield]
  change timedFieldOperator ε
      ⟨(σ ∘ slotSplitVacuumSlot T) q.1,
        quarticLocalLegExternalFieldLabel
          (vac.vertexLabel (slotSplitVacuumOrder T q.1)) q.2⟩ = _
  rw [timedFieldOperator_quarticLocalLeg]
  rfl

private theorem fixedExternalOfSlotSplit_mixedPairContractionValue_vacuumNormalizedPair
    (ε : Mode → ℝ) (β : ℝ)
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T))
    (pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.mixedPairContractionValue ε β τ τ' σ
        (Common.TwoPointDiagram.slotSplitVacuumNormalizedPairEmbedding
          T ext.1 vac τ τ' σ hσ pr) =
      orderedQuarticPairValue ε β vac (slotSplitVacuumOrder T)
        (σ ∘ slotSplitVacuumSlot T) pr.1.1 pr.1.2 := by
  let d := fixedExternalOfSlotSplit T ext vac
  unfold FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    mixedTimeOrderedAtomicPairValue orderedQuarticPairValue
  change (freeGibbsDensityOperator ε β).expectation
      (Common.finiteHilbertOperator
        ((mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence σ
            (mixedTimeOrderedQuarticLegMapPosition
              (slotSplitVacuumSlot T) τ τ' σ pr.1.1)).comp
          (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence σ
            (mixedTimeOrderedQuarticLegMapPosition
              (slotSplitVacuumSlot T) τ τ' σ pr.1.2)))) = _
  rw [fixedExternalOfSlotSplit_mixedAtomicOperator_vacuumOrderedLeg
      ε T ext vac τ τ' σ pr.1.1,
    fixedExternalOfSlotSplit_mixedAtomicOperator_vacuumOrderedLeg
      ε T ext vac τ τ' σ pr.1.2]

private theorem fixedExternalOfSlotSplit_prod_vacuumPairContractionValue_eq
    (ε : Mode → ℝ) (β : ℝ)
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.1.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.1.vacuumComponentParts.prod (fun B =>
        ∏ pr : d.1.MixedComponentPair τ τ' σ B,
          d.mixedPairContractionValue ε β τ τ' σ pr.1) =
      ∏ pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair,
        orderedQuarticPairValue ε β vac (slotSplitVacuumOrder T)
          (σ ∘ slotSplitVacuumSlot T) pr.1.1 pr.1.2 := by
  let d := fixedExternalOfSlotSplit T ext vac
  let F : d.1.MixedVacuumPair τ τ' σ → ℂ := fun pr =>
    d.mixedPairContractionValue ε β τ τ' σ pr.1
  let e := Common.TwoPointDiagram.slotSplitVacuumMixedPairEquiv
    T ext.1 vac hext τ τ' σ hσ
  calc
    d.1.vacuumComponentParts.prod (fun B =>
        ∏ pr : d.1.MixedComponentPair τ τ' σ B,
          d.mixedPairContractionValue ε β τ τ' σ pr.1) =
      ∏ B : ↥d.1.vacuumComponentParts,
        ∏ pr : d.1.MixedComponentPair τ τ' σ B.1,
          d.mixedPairContractionValue ε β τ τ' σ pr.1 := by
      exact Finset.prod_subtype d.1.vacuumComponentParts (fun _ => Iff.rfl) _
    _ = ∏ x : Σ B : ↥d.1.vacuumComponentParts,
        d.1.MixedComponentPair τ τ' σ B.1,
        F (d.1.mixedVacuumPairSigmaEquiv τ τ' σ x) := by
      rw [Fintype.prod_sigma]
      rfl
    _ = ∏ pr : d.1.MixedVacuumPair τ τ' σ, F pr :=
      Equiv.prod_comp (d.1.mixedVacuumPairSigmaEquiv τ τ' σ) F
    _ = ∏ pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair,
        F (e pr) :=
      (Equiv.prod_comp e F).symm
    _ = ∏ pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair,
        orderedQuarticPairValue ε β vac (slotSplitVacuumOrder T)
          (σ ∘ slotSplitVacuumSlot T) pr.1.1 pr.1.2 := by
      apply Fintype.prod_congr
      intro pr
      change d.mixedPairContractionValue ε β τ τ' σ (e pr).1 = _
      rw [Common.TwoPointDiagram.slotSplitVacuumMixedPairEquiv_apply]
      exact fixedExternalOfSlotSplit_mixedPairContractionValue_vacuumNormalizedPair
        ε β T ext vac τ τ' σ hσ pr

/-- For an externally connected left piece and strictly decreasing inherited vacuum times, the
complete product of ambient vacuum-component Dyson fixed-time values is exactly the standalone
fixed-order quartic vacuum integrand, including its Dyson sign and coupling prefactor. -/
theorem fixedExternalOfSlotSplit_prod_vacuumDysonFixedTimeValue_eq_quarticIntegrand
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (hext : ext.1.IsExternallyConnected)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.1.vacuumComponentParts.prod
        (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) =
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
        vac.contractionIntegrand ε β (slotSplitVacuumOrder T)
          (σ ∘ slotSplitVacuumSlot T) := by
  classical
  let d := fixedExternalOfSlotSplit T ext vac
  have hpre :
      d.1.vacuumComponentParts.prod (fun B =>
        d.mixedComponentDysonSign B * d.mixedComponentVertexWeight g B) =
        (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g := by
    simpa [d] using
      (fixedExternalOfSlotSplit_prod_vacuumDysonSign_mul_vertexWeight
        g T ext hext vac)
  have hweight :
      d.1.vacuumComponentParts.prod
          (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ) =
        (vac.pairingInOrder (slotSplitVacuumOrder T)).weight
          Common.Statistics.fermion := by
    let base := Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac
    change base.vacuumComponentParts.prod
        (base.mixedComponentWeight Common.Statistics.fermion τ τ' σ) = _
    let e := Common.slotSplitVacuumComponentEquiv
      (Finset.subset_univ T) ext.1 vac hext
    let orders := vac.componentPartition.partOrdersOfOrder (slotSplitVacuumOrder T)
    let shuffle := vac.fixedOrderComponentShuffle (slotSplitVacuumOrder T)
    calc
      base.vacuumComponentParts.prod
          (base.mixedComponentWeight Common.Statistics.fermion τ τ' σ) =
        ∏ B : ↥base.vacuumComponentParts,
          base.mixedComponentWeight Common.Statistics.fermion τ τ' σ B.1 := by
        exact Finset.prod_subtype base.vacuumComponentParts (fun _ => Iff.rfl) _
      _ = ∏ C : vac.componentPartition.parts,
          base.mixedComponentWeight Common.Statistics.fermion τ τ' σ (e C).1 :=
        (Equiv.prod_comp e (fun B =>
          base.mixedComponentWeight Common.Statistics.fermion τ τ' σ B.1)).symm
      _ = ∏ C : vac.componentPartition.parts,
          ((vac.restrictComponent C.2).pairingInOrder (orders C)).weight
            Common.Statistics.fermion := by
        apply Fintype.prod_congr
        intro C
        rw [Common.slotSplitVacuumComponentEquiv_apply]
        have hcross := Common.TwoPointDiagram.ofSlotSplit_mixedComponentCrossingCount_vacuum_eq
          T ext.1 vac C τ τ' σ hσ
        simpa [base, Common.TwoPointDiagram.mixedComponentWeight, orders] using
          congrArg (fun k : ℕ => (-1 : ℂ) ^ k) hcross
      _ = (vac.pairingInOrder (vac.assembleVertexOrder orders shuffle)).weight
          Common.Statistics.fermion :=
        (vac.pairingInOrder_weight_eq_prod_components
          Common.Statistics.fermion orders shuffle).symm
      _ = (vac.pairingInOrder (slotSplitVacuumOrder T)).weight
          Common.Statistics.fermion := by
        rw [vac.assembleVertexOrder_fixedOrderComponentShuffle]
  have hcontraction :
      d.1.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.1.MixedComponentPair τ τ' σ B,
            d.mixedPairContractionValue ε β τ τ' σ pr.1) =
        ∏ pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair,
          orderedQuarticPairValue ε β vac (slotSplitVacuumOrder T)
            (σ ∘ slotSplitVacuumSlot T) pr.1.1 pr.1.2 := by
    simpa [d] using
      (fixedExternalOfSlotSplit_prod_vacuumPairContractionValue_eq
        ε β T ext vac hext τ τ' σ hσ)
  have hdysonFn :
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ = fun B =>
        d.mixedComponentDysonSign B *
          (d.mixedComponentVertexWeight g B *
            (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
              ∏ pr : d.1.MixedComponentPair τ τ' σ B,
                d.mixedPairContractionValue ε β τ τ' σ pr.1)) := by
    funext B
    rfl
  change d.1.vacuumComponentParts.prod
      (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) = _
  calc
    d.1.vacuumComponentParts.prod
        (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) =
      d.1.vacuumComponentParts.prod (fun B =>
          d.mixedComponentDysonSign B * d.mixedComponentVertexWeight g B) *
        (d.1.vacuumComponentParts.prod
            (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ) *
          d.1.vacuumComponentParts.prod (fun B =>
            ∏ pr : d.1.MixedComponentPair τ τ' σ B,
              d.mixedPairContractionValue ε β τ τ' σ pr.1)) := by
      rw [hdysonFn]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro B _
      ring
    _ = ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g) *
        ((vac.pairingInOrder (slotSplitVacuumOrder T)).weight Common.Statistics.fermion *
          ∏ pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair,
            orderedQuarticPairValue ε β vac (slotSplitVacuumOrder T)
              (σ ∘ slotSplitVacuumSlot T) pr.1.1 pr.1.2) := by
      rw [hpre, hweight, hcontraction]
    _ = (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
        vac.contractionIntegrand ε β (slotSplitVacuumOrder T)
          (σ ∘ slotSplitVacuumSlot T) := by
      have hpairProd :
          (∏ pr ∈ (vac.pairingInOrder (slotSplitVacuumOrder T)).pairs,
              orderedQuarticPairValue ε β vac (slotSplitVacuumOrder T)
                (σ ∘ slotSplitVacuumSlot T) pr.1 pr.2) =
            ∏ pr : (vac.pairingInOrder (slotSplitVacuumOrder T)).NormalizedPair,
              orderedQuarticPairValue ε β vac (slotSplitVacuumOrder T)
                (σ ∘ slotSplitVacuumSlot T) pr.1.1 pr.1.2 := by
        exact Finset.prod_subtype
          (vac.pairingInOrder (slotSplitVacuumOrder T)).pairs (fun _ => Iff.rfl) _
      unfold QuarticWickDiagram.contractionIntegrand Pairing.evaluation
      rw [hpairProd]

end Fermionic
end SecondQuantization
