import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPrefactor
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPairContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumPairWeight

set_option linter.style.header false

/-!
# Fixed-order contraction integrand on the vacuum half of a fixed external-slot fiber

The vacuum half of a reassembled two-point diagram has now been identified at each scalar layer:
`FiberVacuumPrefactor` gives the Dyson sign and coupling product, `FiberVacuumPairWeight` gives the
fermionic crossing weight, and `FiberVacuumPairContraction` gives the complete product of free Gibbs
pair contractions.  This module assembles those three bridges into the standalone fixed-order
quartic contraction integrand used by the normalized vacuum Dyson coefficient.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

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
    (hσ : StrictAnti (σ ∘ fixedExternalVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.1.vacuumComponentParts.prod
        (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) =
      (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
        vac.contractionIntegrand ε β (fixedExternalVacuumOrder T)
          (σ ∘ fixedExternalVacuumSlot T) := by
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
          (d.mixedComponentWeight Common.Statistics.fermion τ τ' σ) =
        (vac.pairingInOrder (fixedExternalVacuumOrder T)).weight
          Common.Statistics.fermion := by
    simpa [d] using
      (fixedExternalOfSlotSplit_prod_vacuumMixedComponentWeight_eq
        T ext vac hext τ τ' σ hσ)
  have hcontraction :
      d.1.vacuumComponentParts.prod (fun B =>
          ∏ pr : d.MixedComponentPair τ τ' σ B,
            d.mixedPairContractionValue ε β τ τ' σ pr.1) =
        ∏ pr : (vac.pairingInOrder (fixedExternalVacuumOrder T)).NormalizedPair,
          orderedQuarticPairValue ε β vac (fixedExternalVacuumOrder T)
            (σ ∘ fixedExternalVacuumSlot T) pr.1.1 pr.1.2 := by
    simpa [d] using
      (fixedExternalOfSlotSplit_prod_vacuumPairContractionValue_eq
        ε β T ext vac hext τ τ' σ hσ)
  change d.1.vacuumComponentParts.prod
      (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) = _
  calc
    d.1.vacuumComponentParts.prod
        (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) =
      d.1.vacuumComponentParts.prod (fun B =>
          d.mixedComponentDysonSign B * d.mixedComponentVertexWeight g B) *
        (d.1.vacuumComponentParts.prod
            (d.mixedComponentWeight Common.Statistics.fermion τ τ' σ) *
          d.1.vacuumComponentParts.prod (fun B =>
            ∏ pr : d.MixedComponentPair τ τ' σ B,
              d.mixedPairContractionValue ε β τ τ' σ pr.1)) := by
      simp only [FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue,
        FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue,
        FixedExternalTwoPointWickDiagram.mixedComponentPairingValue]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro B _
      ring
    _ = ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g) *
        ((vac.pairingInOrder (fixedExternalVacuumOrder T)).weight Common.Statistics.fermion *
          ∏ pr : (vac.pairingInOrder (fixedExternalVacuumOrder T)).NormalizedPair,
            orderedQuarticPairValue ε β vac (fixedExternalVacuumOrder T)
              (σ ∘ fixedExternalVacuumSlot T) pr.1.1 pr.1.2) := by
      rw [hpre, hweight, hcontraction]
    _ = (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
        vac.contractionIntegrand ε β (fixedExternalVacuumOrder T)
          (σ ∘ fixedExternalVacuumSlot T) := by
      have hpairProd :
          (∏ pr ∈ (vac.pairingInOrder (fixedExternalVacuumOrder T)).pairs,
              orderedQuarticPairValue ε β vac (fixedExternalVacuumOrder T)
                (σ ∘ fixedExternalVacuumSlot T) pr.1 pr.2) =
            ∏ pr : (vac.pairingInOrder (fixedExternalVacuumOrder T)).NormalizedPair,
              orderedQuarticPairValue ε β vac (fixedExternalVacuumOrder T)
                (σ ∘ fixedExternalVacuumSlot T) pr.1.1 pr.1.2 := by
        exact Finset.prod_subtype
          (vac.pairingInOrder (fixedExternalVacuumOrder T)).pairs (fun _ => Iff.rfl) _
      unfold QuarticWickDiagram.contractionIntegrand Pairing.evaluation
      rw [hpairProd]
      ring

end Fermionic
end SecondQuantization
