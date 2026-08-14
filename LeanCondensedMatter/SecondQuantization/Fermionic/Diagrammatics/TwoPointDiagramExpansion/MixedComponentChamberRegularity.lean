import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentChamberCombinatorics
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairTimeTransport
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedPairContractionRegularity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonValue

set_option linter.style.header false

/-!
# Chamberwise regularity of mixed component factors

Common owns the chamberwise transport of mixed component positions, normalized pair endpoints,
crossings, and statistics weights.  This module fixes a base chamber and adds only the continuous
free-Gibbs contraction representative and the fermionic component fixed-time/Dyson values.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
/-- Inside one order chamber, canonical transport of a normalized component pair preserves the two
underlying standard atomic legs in their normalized order. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (pr : d.1.MixedComponentPair τ τ' σ B) :
    let q := d.1.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.1 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.1 ∧
      mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.2 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.2 := by
  classical
  let q := d.1.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  let p0 := d.1.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)
  let p1 := d.1.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)
  have hEnds :
      d.1.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p0 ∧
        d.1.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p1 := by
    simpa [q, p0, p1] using
      d.1.mixedComponentPairTimeEquiv_endpoints_eq_of_sameOrderChamber
        τ τ' σ υ B hChamber pr
  have h0Pos :
      q.1.1.1 = (d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p0).1 := by
    simpa [q] using congrArg Subtype.val hEnds.1
  have h1Pos :
      q.1.1.2 = (d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
    simpa [q] using congrArg Subtype.val hEnds.2
  constructor
  · rw [h0Pos]
    simpa [p0] using
      d.1.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p0
  · rw [h1Pos]
    simpa [p1] using
      d.1.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p1

/-- Globally continuous fixed-index representative of one mixed component pairing value based at
`σ₀`. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairingChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ₀ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : (Fin n → ℝ) → ℂ :=
  fun σ =>
    d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ₀ B *
      ∏ pr : d.1.MixedComponentPair τ τ' σ₀ B,
        orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2)

/-- The fixed-index chamber representative is globally continuous on the ambient interaction-time
space. -/
theorem FixedExternalTwoPointWickDiagram.continuous_mixedComponentPairingChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ₀ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) :
    Continuous (d.mixedComponentPairingChamberRepresentative ε β τ τ' σ₀ B) := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentPairingChamberRepresentative
  exact continuous_const.mul
    (continuous_finsetProd _ fun pr _ =>
      continuous_orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.1)
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ₀ pr.1.1.2))

/-- On the base mixed-order chamber, the globally continuous fixed-index representative agrees with
the actual component pairing value. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingChamberRepresentative_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ₀ σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ₀ σ) :
    d.mixedComponentPairingChamberRepresentative ε β τ τ' σ₀ B σ =
      d.mixedComponentPairingValue ε β τ τ' σ B := by
  classical
  unfold FixedExternalTwoPointWickDiagram.mixedComponentPairingChamberRepresentative
  rw [d.mixedComponentPairingValue_eq_weight_mul_contractionProduct,
    d.1.mixedComponentWeight_eq_of_sameOrderChamber
      Common.Statistics.fermion τ τ' σ₀ σ B hChamber]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentContractionProduct
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
        d.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
          τ τ' σ₀ σ B hChamber pr
      rw [d.mixedPairContractionValue_eq_orderedTwoPointLegPairContraction]
      rw [hLegs.1, hLegs.2]
    _ = ∏ q : d.1.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ q.1 := by
      exact Equiv.prod_comp e
        (fun q : d.1.MixedComponentPair τ τ' σ B =>
          d.mixedPairContractionValue ε β τ τ' σ q.1)

/-- Continuous chamber representative of one coupling-weighted component fixed-time value. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    (Fin n → ℝ) → ℂ :=
  fun σ => d.mixedComponentVertexWeight g B *
    d.mixedComponentPairingChamberRepresentative ε β τ τ' σ₀ B σ

/-- The fixed-time chamber representative is globally continuous. -/
theorem FixedExternalTwoPointWickDiagram.continuous_mixedComponentFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    Continuous (d.mixedComponentFixedTimeChamberRepresentative ε β g τ τ' σ₀ B) := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeChamberRepresentative
  exact continuous_const.mul
    (d.continuous_mixedComponentPairingChamberRepresentative ε β τ τ' σ₀ B)

/-- On the base chamber, the fixed-time representative agrees with the actual component fixed-time
value. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeChamberRepresentative_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ₀ σ) :
    d.mixedComponentFixedTimeChamberRepresentative ε β g τ τ' σ₀ B σ =
      d.mixedComponentFixedTimeValue ε β g τ τ' σ B := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeChamberRepresentative
    FixedExternalTwoPointWickDiagram.mixedComponentFixedTimeValue
  rw [d.mixedComponentPairingChamberRepresentative_eq_of_sameOrderChamber
    ε β τ τ' σ₀ σ B hChamber]

/-- Continuous chamber representative of the Dyson-signed component fixed-time value. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    (Fin n → ℝ) → ℂ :=
  fun σ => d.mixedComponentDysonSign B *
    d.mixedComponentFixedTimeChamberRepresentative ε β g τ τ' σ₀ B σ

/-- The Dyson-signed chamber representative is globally continuous. -/
theorem FixedExternalTwoPointWickDiagram.continuous_mixedComponentDysonFixedTimeChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ) (B : d.1.componentPartition.parts) :
    Continuous (d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ' σ₀ B) := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
  exact continuous_const.mul
    (d.continuous_mixedComponentFixedTimeChamberRepresentative ε β g τ τ' σ₀ B)

/-- On the base chamber, the Dyson-signed representative agrees with the actual component factor. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ σ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ₀ σ) :
    d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ' σ₀ B σ =
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeChamberRepresentative
    FixedExternalTwoPointWickDiagram.mixedComponentDysonFixedTimeValue
  rw [d.mixedComponentFixedTimeChamberRepresentative_eq_of_sameOrderChamber
    ε β g τ τ' σ₀ σ B hChamber]

end Fermionic
end SecondQuantization
