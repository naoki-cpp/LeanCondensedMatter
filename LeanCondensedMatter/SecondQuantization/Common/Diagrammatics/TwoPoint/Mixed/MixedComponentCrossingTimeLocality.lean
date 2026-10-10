import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber

set_option linter.style.header false

/-!
# Component-locality of mixed pair crossings and order chambers

Canonical transport of component-local normalized pairs preserves their endpoint legs whenever the
component-position order is preserved. Consequently both endpoint data and exchange weights are
invariant under transport within a fixed mixed-order chamber.

These statements depend only on the mixed ordering, component decomposition, and pairing geometry.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*}

/-- In one mixed-order chamber, time transport leaves the ambient normalized pair unchanged. -/
private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_pair_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.1 = pr.1.1 := by
  have hlegs := mixedTimeOrderedAtomicLegEquiv_eq_of_comparisons τ τ' σ υ hChamber
  have hambient : mixedTimeAmbientPositionEquiv τ τ' σ =
      mixedTimeAmbientPositionEquiv τ τ' υ := by
    unfold mixedTimeAmbientPositionEquiv standardToMixedAtomicPositionEquiv
    rw [hlegs]
  have hpairing : d.pairingInMixedOrder τ τ' σ =
      d.pairingInMixedOrder τ τ' υ := by
    unfold TwoPointDiagram.pairingInMixedOrder
    rw [hambient]
  change ((d.pairingInMixedOrder τ τ' υ).pairEndpointEquiv.symm
    (((mixedTimeAmbientPositionEquiv τ τ' σ).trans
      (mixedTimeAmbientPositionEquiv τ τ' υ).symm)
      ((d.pairingInMixedOrder τ τ' σ).pairEndpointEquiv (pr.1, 0)))).1.1 =
    pr.1.1
  simp only [Equiv.trans_apply, hambient, Equiv.symm_apply_apply]
  rw [← hpairing]
  simp only [Equiv.symm_apply_apply]

/-- Inside one order chamber, canonical transport of a normalized component pair preserves the two
underlying standard atomic legs in their normalized order. -/
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.1 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.1 ∧
      mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.2 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.2 := by
  have hPair := d.mixedComponentPairTimeEquiv_pair_eq_of_sameOrderChamber
    τ τ' σ υ B hChamber pr
  have hlegs := mixedTimeOrderedAtomicLegEquiv_eq_of_comparisons τ τ' σ υ hChamber
  constructor
  · simpa only [hlegs] using
      congrArg (fun p => mixedTimeOrderedAtomicLegEquiv τ τ' υ p.1) hPair
  · simpa only [hlegs] using
      congrArg (fun p => mixedTimeOrderedAtomicLegEquiv τ τ' υ p.2) hPair

/-- Component exchange-statistics weight is constant on one chamber. -/
theorem TwoPointDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B := by
  have hlegs := mixedTimeOrderedAtomicLegEquiv_eq_of_comparisons τ τ' σ υ hChamber
  have hambient : mixedTimeAmbientPositionEquiv τ τ' σ =
      mixedTimeAmbientPositionEquiv τ τ' υ := by
    unfold mixedTimeAmbientPositionEquiv standardToMixedAtomicPositionEquiv
    rw [hlegs]
  let weightFor (e : Fin (2 * (2 * n + 1)) ≃
      Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) : ℂ :=
    (s.zetaInt : ℂ) ^
      Pairing.componentCrossingCount (d.pairing.transport e)
        (Equiv.sigmaFiberEquiv (fun pr =>
          (⟨d.vertexGraph.componentBlock
              (twoPointVertexOfLeg (e pr.1.1)),
            d.vertexGraph.componentBlock_mem_componentPartition _⟩ :
              d.vertexGraph.componentPartition.parts))) B B
  change weightFor (mixedTimeAmbientPositionEquiv τ τ' σ) =
    weightFor (mixedTimeAmbientPositionEquiv τ τ' υ)
  exact congrArg weightFor hambient
end Common
end SecondQuantization
