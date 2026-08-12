import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing

set_option linter.style.header false

/-!
# Normalized vacuum pairs inside the ambient mixed pairing

For a fixed external-slot fiber with strictly ordered inherited vacuum times, the inherited quartic
vacuum pairing embeds into the ambient mixed two-point pairing.  The endpoint map is strictly
monotone, so normalized-pair membership and crossing geometry are both preserved without any new
pairing decomposition.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} {n : ℕ} {i j : Mode}

/-- Embed a normalized pair of the fixed-order quartic vacuum pairing into the ambient mixed
pairing. -/
noncomputable def fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T)) :
    (vac.pairingInOrder (fixedExternalVacuumOrder T)).NormalizedPair ↪
      ((fixedExternalOfSlotSplit T ext vac).pairingInMixedOrder τ τ' σ).NormalizedPair where
  toFun pr :=
    ⟨(mixedTimeOrderedQuarticLegMapPosition (fixedExternalVacuumSlot T) τ τ' σ pr.1.1,
      mixedTimeOrderedQuarticLegMapPosition (fixedExternalVacuumSlot T) τ τ' σ pr.1.2),
      (fixedExternalOfSlotSplit_mem_mixedPairs_vacuumOrderedLeg_iff
        T ext vac τ τ' σ hσ pr.1.1 pr.1.2).2 pr.2⟩
  inj' := by
    intro p q hpq
    have hE : StrictMono (mixedTimeOrderedQuarticLegMapPosition
        (fixedExternalVacuumSlot T) τ τ' σ) :=
      mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
        (fixedExternalVacuumSlot T) (fixedExternalVacuumSlot_strictMono T)
        τ τ' σ hσ
    apply Subtype.ext
    apply Prod.ext
    · apply hE.injective
      exact congrArg (fun z => z.1.1) hpq
    · apply hE.injective
      exact congrArg (fun z => z.1.2) hpq

@[simp]
theorem fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding_apply
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T))
    (pr : (vac.pairingInOrder (fixedExternalVacuumOrder T)).NormalizedPair) :
    (fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding
      T ext vac τ τ' σ hσ pr).1 =
      (mixedTimeOrderedQuarticLegMapPosition
          (fixedExternalVacuumSlot T) τ τ' σ pr.1.1,
        mixedTimeOrderedQuarticLegMapPosition
          (fixedExternalVacuumSlot T) τ τ' σ pr.1.2) :=
  rfl

/-- The vacuum normalized-pair embedding preserves and reflects crossings. -/
theorem fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding_crosses_iff
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T))
    (p q : (vac.pairingInOrder (fixedExternalVacuumOrder T)).NormalizedPair) :
    Crosses
        (fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding
          T ext vac τ τ' σ hσ p).1
        (fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding
          T ext vac τ τ' σ hσ q).1 ↔
      Crosses p.1 q.1 := by
  let E := mixedTimeOrderedQuarticLegMapPosition
    (fixedExternalVacuumSlot T) τ τ' σ
  have hE : StrictMono E :=
    mixedTimeOrderedQuarticLegMapPosition_strictMono_of_strictAnti
      (fixedExternalVacuumSlot T) (fixedExternalVacuumSlot_strictMono T)
      τ τ' σ hσ
  simpa [fixedExternalOfSlotSplitVacuumNormalizedPairEmbedding, E] using
    (crosses_map_iff E hE p.1.1 p.1.2 q.1.1 q.1.2)

end Fermionic
end SecondQuantization
