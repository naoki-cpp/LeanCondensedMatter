import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPairTimeTransport
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairingValue

set_option linter.style.header false

/-!
# Fermionic contraction transport across interaction-time assignments

Common owns canonical mixed-component pair transport and crossing/weight covariance. This module adds
only the finite Gibbs contraction data needed to transport fermionic component pairing values.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The canonical pair transport preserves the finite Gibbs contraction attached to every pair. -/
def FixedExternalTwoPointWickDiagram.MixedComponentContractionPreserving
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : Prop :=
  ∀ p : d.1.MixedComponentPair τ τ' σ B,
    d.mixedPairContractionValue ε β τ τ' σ p.1 =
      d.mixedPairContractionValue ε β τ τ' υ
        (d.1.mixedComponentPairTimeEquiv τ τ' σ υ B p).1

/-- Product of finite Gibbs contractions internal to one full component. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentContractionProduct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) : ℂ :=
  ∏ pr : d.1.MixedComponentPair τ τ' σ B,
    d.mixedPairContractionValue ε β τ τ' σ pr.1

/-- Contraction preservation under the canonical time transport gives equality of the complete
component pair-contraction products. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentContractionProduct_eq_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hContraction : d.MixedComponentContractionPreserving ε β τ τ' σ υ B) :
    d.mixedComponentContractionProduct ε β τ τ' σ B =
      d.mixedComponentContractionProduct ε β τ τ' υ B := by
  classical
  let e := d.1.mixedComponentPairTimeEquiv τ τ' σ υ B
  unfold FixedExternalTwoPointWickDiagram.mixedComponentContractionProduct
  calc
    (∏ p : d.1.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' σ p.1) =
      ∏ p : d.1.MixedComponentPair τ τ' σ B,
        d.mixedPairContractionValue ε β τ τ' υ (e p).1 := by
      apply Fintype.prod_congr
      intro p
      exact hContraction p
    _ = ∏ q : d.1.MixedComponentPair τ τ' υ B,
        d.mixedPairContractionValue ε β τ τ' υ q.1 := by
      exact Equiv.prod_comp e
        (fun q : d.1.MixedComponentPair τ τ' υ B =>
          d.mixedPairContractionValue ε β τ τ' υ q.1)

/-- The mixed component pairing value is its internal crossing weight times its component
contraction product. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_eq_weight_mul_contractionProduct
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) :
    d.mixedComponentPairingValue ε β τ τ' σ B =
      d.1.mixedComponentWeight Common.Statistics.fermion τ τ' σ B *
        d.mixedComponentContractionProduct ε β τ τ' σ B := by
  rfl

/-- Preservation of Common-owned crossings and fermionic contractions under canonical time
transport gives equality of complete mixed component pairing values. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_eq_of_timeTransport
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hCross : d.1.MixedComponentCrossingPreserving τ τ' σ υ B)
    (hContraction : d.MixedComponentContractionPreserving ε β τ τ' σ υ B) :
    d.mixedComponentPairingValue ε β τ τ' σ B =
      d.mixedComponentPairingValue ε β τ τ' υ B := by
  rw [d.mixedComponentPairingValue_eq_weight_mul_contractionProduct,
    d.mixedComponentPairingValue_eq_weight_mul_contractionProduct,
    d.1.mixedComponentWeight_eq_of_timeTransport Common.Statistics.fermion
      τ τ' σ υ B hCross,
    d.mixedComponentContractionProduct_eq_of_timeTransport
      ε β τ τ' σ υ B hContraction]

end Fermionic
end SecondQuantization
