import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPrefactor
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.TwoPointLegEmbedding
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Ordered

set_option linter.style.header false

/-!
# Pairing transport for the quartic vacuum half of a fixed external-slot fiber

The quartic vacuum half of `fixedExternalOfSlotSplit` carries the right pairing of the canonical
slot split. Its inherited increasing vertex order therefore embeds its fixed ordered legs into the
ambient two-point standard legs through the Common-owned quartic/two-point leg embedding, and the
embedding intertwines the quartic fixed-order partner with the ambient two-point partner.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

/-- The increasing inherited order on the quartic complement of a chosen external-slot set. -/
noncomputable def fixedExternalVacuumOrder (T : Finset (Fin n)) :
    Common.QuarticVertexOrder ((Finset.univ : Finset (Fin n)) \ T) :=
  (((Finset.univ : Finset (Fin n)) \ T).orderIsoOfFin rfl).toEquiv

/-- The ambient interaction slot occupied by one local slot in the inherited vacuum order. -/
noncomputable def fixedExternalVacuumSlot (T : Finset (Fin n)) :
    Fin ((Finset.univ : Finset (Fin n)) \ T).card → Fin n :=
  fun k => (fixedExternalVacuumOrder T k).1

omit [LinearOrder Mode] [Fintype Mode] in
/-- The inherited vacuum-slot map is strictly increasing in ambient interaction-slot order. -/
theorem fixedExternalVacuumSlot_strictMono (T : Finset (Fin n)) :
    StrictMono (fixedExternalVacuumSlot T) := by
  intro a b hab
  simpa [fixedExternalVacuumSlot, fixedExternalVacuumOrder] using
    (((Finset.univ : Finset (Fin n)) \ T).orderIsoOfFin rfl).strictMono hab

omit [LinearOrder Mode] [Fintype Mode] in
/-- A fixed-order quartic vacuum leg, viewed as an ambient standard two-point leg, is exactly the
right-leg embedding of the canonical slot split. -/
theorem fixedExternalVacuumOrderedLeg_eq_slotSplitRight
    (T : Finset (Fin n))
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
        (orderedQuarticLegMapToTwoPointLeg (fixedExternalVacuumSlot T) p) =
      Common.slotLegSplitting (Finset.subset_univ T)
        (Sum.inr
          (Common.orderedLegToDiagramLeg
            ((Finset.univ : Finset (Fin n)) \ T) (fixedExternalVacuumOrder T) p)) := by
  let q := Common.orderedQuarticLegEquiv
    ((Finset.univ : Finset (Fin n)) \ T).card p
  have hp :
      (Common.orderedQuarticLegEquiv
        ((Finset.univ : Finset (Fin n)) \ T).card).symm q = p :=
    (Common.orderedQuarticLegEquiv
      ((Finset.univ : Finset (Fin n)) \ T).card).symm_apply_apply p
  rw [← hp]
  rcases q with ⟨v, l⟩
  have hordered :
      Common.orderedLegToDiagramLeg
          ((Finset.univ : Finset (Fin n)) \ T) (fixedExternalVacuumOrder T)
          ((Common.orderedQuarticLegEquiv
            ((Finset.univ : Finset (Fin n)) \ T).card).symm (v, l)) =
        (Common.quarticLegEquiv ((Finset.univ : Finset (Fin n)) \ T)).symm
          (fixedExternalVacuumOrder T v, l) := by
    simp [Common.orderedLegToDiagramLeg]
  rw [hordered, Common.slotLegSplitting_right_interaction]
  simp [orderedQuarticLegMapToTwoPointLeg, orderedQuarticLegToTwoPointLeg,
    fixedExternalVacuumSlot]

omit [LinearOrder Mode] [Fintype Mode] in
/-- The ambient standard-leg partner on the vacuum side is the fixed-order quartic partner embedded
back into the ambient two-point leg enumeration. -/
theorem fixedExternalOfSlotSplit_atomicLegPartner_vacuumOrderedLeg
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.atomicLegPartner (orderedQuarticLegMapToTwoPointLeg (fixedExternalVacuumSlot T) p) =
      orderedQuarticLegMapToTwoPointLeg (fixedExternalVacuumSlot T)
        ((vac.pairingInOrder (fixedExternalVacuumOrder T)).partner p) := by
  let d := fixedExternalOfSlotSplit T ext vac
  apply (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm.injective
  rw [FixedExternalTwoPointWickDiagram.atomicLegPartner, Equiv.symm_apply_apply]
  rw [fixedExternalVacuumOrderedLeg_eq_slotSplitRight T p,
    fixedExternalVacuumOrderedLeg_eq_slotSplitRight T
      ((vac.pairingInOrder (fixedExternalVacuumOrder T)).partner p)]
  change (Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac).pairing.partner
      (Common.slotLegSplitting (Finset.subset_univ T)
        (Sum.inr (Common.orderedLegToDiagramLeg
          ((Finset.univ : Finset (Fin n)) \ T) (fixedExternalVacuumOrder T) p))) = _
  rw [Common.TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inr]
  apply congrArg (fun q =>
    Common.slotLegSplitting (Finset.subset_univ T) (Sum.inr q))
  rw [Common.QuarticDiagram.pairingInOrder, Pairing.relabel_partner,
    Equiv.apply_symm_apply]

omit [LinearOrder Mode] [Fintype Mode] in
/-- The mixed-order partner on the reassembled diagram is the mixed position of the corresponding
fixed-order quartic vacuum partner. -/
theorem fixedExternalOfSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := fixedExternalOfSlotSplit T ext vac
    (d.pairingInMixedOrder τ τ' σ).partner
        (mixedTimeOrderedQuarticLegMapPosition
          (fixedExternalVacuumSlot T) τ τ' σ p) =
      mixedTimeOrderedQuarticLegMapPosition
        (fixedExternalVacuumSlot T) τ τ' σ
        ((vac.pairingInOrder (fixedExternalVacuumOrder T)).partner p) := by
  let d := fixedExternalOfSlotSplit T ext vac
  change (d.pairingInMixedOrder τ τ' σ).partner
      (mixedTimeOrderedAtomicLegPosition τ τ' σ
        (orderedQuarticLegMapToTwoPointLeg (fixedExternalVacuumSlot T) p)) = _
  rw [d.pairingInMixedOrder_partner_legPosition,
    fixedExternalOfSlotSplit_atomicLegPartner_vacuumOrderedLeg T ext vac p]
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- On a strictly ordered inherited vacuum-time assignment, a local fixed-order quartic pair is
normalized if and only if its two endpoints form the corresponding normalized pair in the ambient
mixed two-point pairing. -/
theorem fixedExternalOfSlotSplit_mem_mixedPairs_vacuumOrderedLeg_iff
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T))
    (a b : Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))) :
    let d := fixedExternalOfSlotSplit T ext vac
    (mixedTimeOrderedQuarticLegMapPosition (fixedExternalVacuumSlot T) τ τ' σ a,
        mixedTimeOrderedQuarticLegMapPosition (fixedExternalVacuumSlot T) τ τ' σ b) ∈
      (d.pairingInMixedOrder τ τ' σ).pairs ↔
    (a, b) ∈ (vac.pairingInOrder (fixedExternalVacuumOrder T)).pairs := by
  let d := fixedExternalOfSlotSplit T ext vac
  let E := mixedTimeOrderedQuarticLegMapPosition
    (fixedExternalVacuumSlot T) τ τ' σ
  have hE : StrictMono E :=
    mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
      (fixedExternalVacuumSlot T) (fixedExternalVacuumSlot_strictMono T)
      τ τ' σ hσ
  let e :
      Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card)) ↪o
        Fin (2 * (2 * n + 1)) :=
    OrderEmbedding.ofStrictMono E hE
  change (E a, E b) ∈ (d.pairingInMixedOrder τ τ' σ).pairs ↔
    (a, b) ∈ (vac.pairingInOrder (fixedExternalVacuumOrder T)).pairs
  rw [Pairing.mem_pairs_iff, Pairing.mem_pairs_iff]
  constructor
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mp hab, ?_⟩
    apply e.injective
    change E ((vac.pairingInOrder (fixedExternalVacuumOrder T)).partner a) = E b
    calc
      E ((vac.pairingInOrder (fixedExternalVacuumOrder T)).partner a) =
          (d.pairingInMixedOrder τ τ' σ).partner (E a) :=
        (fixedExternalOfSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
          T ext vac τ τ' σ a).symm
      _ = E b := hpartner
  · rintro ⟨hab, hpartner⟩
    refine ⟨e.lt_iff_lt.mpr hab, ?_⟩
    rw [fixedExternalOfSlotSplit_pairingInMixedOrder_partner_vacuumOrderedLeg
      T ext vac τ τ' σ a, hpartner]

end Fermionic
end SecondQuantization
