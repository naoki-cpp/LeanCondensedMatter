import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumPairImage
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPrefactor
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPairContractionRegularity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Pair contractions on the vacuum half of a fixed external-slot fiber

The Common vacuum-pair equivalence identifies which ambient mixed pair corresponds to every
fixed-order quartic vacuum pair. This module keeps only the fermionic scalar-contraction transport.
The proof is operator-local: the ambient standard leg carries the same quartic vertex label, local
leg, and inherited imaginary time as the standalone quartic leg.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

omit [LinearOrder Mode] [Fintype Mode] in
/-- The reassembled fixed-external diagram has the standalone vacuum vertex label at every inherited
vacuum slot. -/
theorem fixedExternalOfSlotSplit_vertexLabelSequence_vacuumSlot
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (v : Fin ((Finset.univ : Finset (Fin n)) \ T).card) :
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

omit [LinearOrder Mode] [Fintype Mode] in
/-- At an inherited quartic vacuum leg, the mixed standard-leg field descriptor is exactly the
standalone quartic field at the inherited local time. -/
theorem fixedExternalOfSlotSplit_orderedTwoPointLegField_vacuumOrderedLeg
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let q := Common.orderedQuarticLegEquiv
      ((Finset.univ : Finset (Fin n)) \ T).card p
    orderedTwoPointLegField i j τ τ'
        (fixedExternalOfSlotSplit T ext vac).vertexLabelSequence σ
        (orderedQuarticLegMapToTwoPointLeg (slotSplitVacuumSlot T) p) =
      ⟨(σ ∘ slotSplitVacuumSlot T) q.1,
        quarticLocalLegExternalFieldLabel
          (vac.vertexLabel (slotSplitVacuumOrder T q.1)) q.2⟩ := by
  let q := Common.orderedQuarticLegEquiv
    ((Finset.univ : Finset (Fin n)) \ T).card p
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
  rw [fixedExternalOfSlotSplit_vertexLabelSequence_vacuumSlot T ext vac v]
  simp

omit [Fintype Mode] in
/-- The mixed atomic operator at an inherited vacuum leg is the standalone fixed-order quartic leg
operator. -/
theorem fixedExternalOfSlotSplit_mixedAtomicOperator_vacuumOrderedLeg
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
  rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition,
    fixedExternalOfSlotSplit_orderedTwoPointLegField_vacuumOrderedLeg T ext vac τ τ' σ p]
  let q := Common.orderedQuarticLegEquiv
    ((Finset.univ : Finset (Fin n)) \ T).card p
  change timedFieldOperator ε
      ⟨(σ ∘ slotSplitVacuumSlot T) q.1,
        quarticLocalLegExternalFieldLabel
          (vac.vertexLabel (slotSplitVacuumOrder T q.1)) q.2⟩ = _
  rw [timedFieldOperator_quarticLocalLeg]
  rfl

/-- Each standalone fixed-order quartic vacuum pair has exactly the same free Gibbs contraction as
its image in the ambient mixed two-point pairing. -/
theorem fixedExternalOfSlotSplit_mixedPairContractionValue_vacuumNormalizedPair
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

/-- The complete contraction product over all ambient vacuum-component pairs is the contraction
product of the standalone fixed-order quartic vacuum pairing. -/
theorem fixedExternalOfSlotSplit_prod_vacuumPairContractionValue_eq
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

end Fermionic
end SecondQuantization
