import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplitVacuumComponentPair
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPrefactor
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity

set_option linter.style.header false

/-!
# Fermionic pairing weight on the vacuum half of a fixed external-slot fiber

Common owns fixed-order quartic component-pair embeddings, the slot-split vacuum component-pair
equivalence, and componentwise crossing-count transport. This module applies those structural facts
to the fermionic statistics weight and identifies the product of ambient vacuum-component weights
with the standalone fixed-order quartic vacuum pairing weight.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} {n : ℕ} {i j : Mode}

/-- The product of all ambient vacuum-component fermionic weights is the weight of the standalone
fixed-order quartic vacuum pairing. -/
theorem fixedExternalOfSlotSplit_prod_vacuumMixedComponentWeight_eq
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (hext : ext.1.IsExternallyConnected)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.1.vacuumComponentParts.prod
        (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ) =
      (vac.pairingInOrder (slotSplitVacuumOrder T)).weight Common.Statistics.fermion := by
  let base := Common.TwoPointDiagram.ofSlotSplit (Finset.subset_univ T) ext.1 vac
  change base.vacuumComponentParts.prod
      (base.mixedComponentWeight Common.Statistics.fermion τ τ' σ) = _
  let e := Common.slotSplitVacuumComponentEquiv
    (Finset.subset_univ T) ext.1 vac hext
  let orders := vac.componentVertexOrdersOfVertexOrder (slotSplitVacuumOrder T)
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

end Fermionic
end SecondQuantization
