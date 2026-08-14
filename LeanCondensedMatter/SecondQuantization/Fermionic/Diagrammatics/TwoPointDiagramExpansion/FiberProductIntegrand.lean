import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPieceAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumIntegrand

set_option linter.style.header false

/-!
# Product integrand on a fixed external-slot fiber

The canonical component factorization separates a reassembled fixed-external two-point diagram into
its external component and its vacuum components. `ExternalPieceAmplitude` identifies the signed
external factor with the standalone external piece, while `FiberVacuumIntegrand` identifies the
complete signed vacuum-component product with the standalone fixed-order quartic vacuum integrand.

This module combines those two already-established bridges into the pointwise product identity used
by the coefficientwise Cauchy-product step of the linked-cluster theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {n : ℕ} {i j : Mode}

/-- For an externally connected left piece and strictly decreasing inherited vacuum times, the
signed fixed-time amplitude of the reassembled diagram is the product of the standalone external
piece amplitude and the standalone fixed-order quartic vacuum integrand. -/
theorem fixedExternalOfSlotSplit_dysonFixedTimeAmplitude_eq_externalPiece_mul_quarticIntegrand
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (hext : ext.1.IsExternallyConnected)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.externalPieceTimes σ) *
        ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
          vac.contractionIntegrand ε β (slotSplitVacuumOrder T)
            (σ ∘ slotSplitVacuumSlot T)) := by
  classical
  let d := fixedExternalOfSlotSplit T ext vac
  change d.dysonFixedTimeAmplitude ε β g τ τ' σ = _
  rw [d.dysonFixedTimeAmplitude_eq_external_mul_prod_vacuum ε β g τ τ' σ,
    d.mixedExternalDysonFixedTimeValue_eq_externalPiece ε β g τ τ' σ]
  have hvac :
      d.1.vacuumComponentParts.prod
          (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) =
        (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
          vac.contractionIntegrand ε β (slotSplitVacuumOrder T)
            (σ ∘ slotSplitVacuumSlot T) := by
    simpa [d] using
      (fixedExternalOfSlotSplit_prod_vacuumDysonFixedTimeValue_eq_quarticIntegrand
        ε β g T ext hext vac τ τ' σ hσ)
  rw [hvac]

end Fermionic
end SecondQuantization
