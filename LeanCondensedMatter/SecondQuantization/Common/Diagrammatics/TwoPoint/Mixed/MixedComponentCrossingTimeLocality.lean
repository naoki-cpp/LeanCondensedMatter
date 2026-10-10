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
  have hstd : standardToMixedAtomicPositionEquiv τ τ' σ =
      standardToMixedAtomicPositionEquiv τ τ' υ := by
    unfold standardToMixedAtomicPositionEquiv
    rw [hlegs]
  have hambient : mixedTimeAmbientPositionEquiv τ τ' σ =
      mixedTimeAmbientPositionEquiv τ τ' υ := by
    unfold mixedTimeAmbientPositionEquiv
    rw [hstd]
  let f := (mixedTimeAmbientPositionEquiv τ τ' σ).trans
    (mixedTimeAmbientPositionEquiv τ τ' υ).symm
  have hf (p : Fin (2 * (2 * n + 1))) : f p = p := by
    simp only [f, hambient, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hPair := d.mixedPairTimeEquiv_pair_eq_or_swap τ τ' σ υ pr.1
  change (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.1 =
      (f pr.1.1.1, f pr.1.1.2) ∨
    (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.1 =
      (f pr.1.1.2, f pr.1.1.1) at hPair
  simp only [hf] at hPair
  rcases hPair with h | h
  · exact h
  · have hSource : pr.1.1.1 < pr.1.1.2 :=
      ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff pr.1.1.1 pr.1.1.2).mp pr.1.2 |>.1
    have hTarget :
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.1.1 <
          (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.1.2 :=
      ((d.pairingInMixedOrder τ τ' υ).mem_pairs_iff
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.1.1
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.1.2).mp
          (d.mixedComponentPairTimeEquiv τ τ' σ υ B pr).1.2 |>.1
    rw [congrArg Prod.fst h, congrArg Prod.snd h] at hTarget
    exact (lt_asymm hTarget hSource).elim

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
      congrArg (mixedTimeOrderedAtomicLegEquiv τ τ' υ ∘ Prod.fst) hPair
  · simpa only [hlegs] using
      congrArg (mixedTimeOrderedAtomicLegEquiv τ τ' υ ∘ Prod.snd) hPair

/-- Component exchange-statistics weight is constant on one chamber. -/
theorem TwoPointDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B := by
  unfold TwoPointDiagram.mixedComponentWeight
  congr 1
  unfold TwoPointDiagram.mixedComponentCrossingCount
  simp only [Pairing.componentCrossingCount, Fintype.sum_prod_type]
  exact sum_sum_crosses_eq_of_equiv
    (fun p : d.MixedComponentPair τ τ' σ B => p.1.1)
    (fun p : d.MixedComponentPair τ τ' υ B => p.1.1)
    (d.mixedComponentPairTimeEquiv τ τ' σ υ B)
    (fun p q => by
      rw [d.mixedComponentPairTimeEquiv_pair_eq_of_sameOrderChamber
          τ τ' σ υ B hChamber p,
        d.mixedComponentPairTimeEquiv_pair_eq_of_sameOrderChamber
          τ τ' σ υ B hChamber q])
end Common
end SecondQuantization
