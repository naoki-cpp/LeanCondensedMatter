import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossingTimeLocality
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairTimeTransport
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPairContractionRegularity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue

set_option linter.style.header false

/-!
# Chamberwise regularity of mixed component factors

Common owns the chamberwise transport of mixed component positions, normalized pair endpoints,
endpoint legs, crossings, and statistics weights. This module fixes a base chamber and adds only the
continuous free-Gibbs contraction representative and the fermionic Dyson-signed component value.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Continuous chamber representative of the Dyson-signed component fixed-time value. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    (Fin n → ℝ) → ℂ :=
  fun σ => d.mixedComponentDysonSign B *
    (d.mixedComponentVertexWeight g B *
      (d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ₀ B *
        ∏ pr : d.1.MixedComponentPair τ τ' σ₀ B,
          orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence σ
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2)))

/-- The Dyson-signed chamber representative is globally continuous. -/
theorem FixedExternalTwoPointWickDiagram.continuous_mixedComponentDysonFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    Continuous (d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ' σ₀ B) := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
  exact continuous_const.mul
    (continuous_const.mul
      (continuous_const.mul
        (continuous_finsetProd _ fun pr _ =>
          continuous_orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
            (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2))))

/-- On the base chamber, the Dyson-signed representative agrees with the actual component factor. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ₀ σ) :
    d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ' σ₀ B σ =
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
  classical
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
    FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
    FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
    FixedExternalTwoPointWickDiagram.mixedComponentPairingValue
  apply congrArg (fun z : ℂ =>
    d.mixedComponentDysonSign B * (d.mixedComponentVertexWeight g B * z))
  rw [d.1.mixedComponentWeight_eq_of_sameOrderChamber
    Common.Statistics.fermion τ τ' σ₀ σ B hChamber]
  apply congrArg (fun z : ℂ =>
    d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B * z)
  let e := d.1.mixedComponentPairTimeEquiv τ τ' σ₀ σ B
  calc
    (∏ pr : d.1.MixedComponentPair τ τ' σ₀ B,
        orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2)) =
      ∏ pr : d.1.MixedComponentPair τ τ' σ₀ B,
        d.mixedPairContractionValue ε β τ τ' σ (e pr).1 := by
      apply Fintype.prod_congr
      intro pr
      have hLegs :=
        d.1.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
          τ τ' σ₀ σ B hChamber pr
      rw [d.mixedPairContractionValue_eq_orderedTwoPointLegPairContraction]
      rw [hLegs.1, hLegs.2]
    _ = ∏ q : d.1.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ q.1 := by
      exact Equiv.prod_comp e
        (fun q : d.1.MixedComponentPair τ τ' σ B =>
          d.mixedPairContractionValue ε β τ τ' σ q.1)

end Fermionic
end SecondQuantization
