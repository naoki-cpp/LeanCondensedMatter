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

/-- Canonical comparison of mixed positions of one full component across interaction-time
assignments, used only to prove chamber locality. -/
private noncomputable def TwoPointDiagram.mixedComponentPositionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.MixedComponentPosition τ τ' υ B :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.mixedComponentPositionEquiv τ τ' υ B).symm

/-- Time transport preserves the atomic leg represented by a mixed component position. -/
private theorem TwoPointDiagram.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    mixedTimeOrderedAtomicLegEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 := by
  rw [← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv]
  apply congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
  have h := congrArg Subtype.val
    (show d.mixedComponentPositionEquiv τ τ' υ B
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
        d.mixedComponentPositionEquiv τ τ' σ B p by
      simp [TwoPointDiagram.mixedComponentPositionTimeEquiv])
  change mixedTimeAmbientPositionEquiv τ τ' υ
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
    mixedTimeAmbientPositionEquiv τ τ' σ p.1 at h
  exact h

/-- Component position transport preserves strict order inside one mixed-order chamber. -/
private theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 := by
  have hOrder :
      (mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) <
        mixedTimeOrderedAtomicLegPosition τ τ' σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1)) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1) <
        mixedTimeOrderedAtomicLegPosition τ τ' υ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1)) :=
    mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff τ τ' σ υ _ _
      (orderedTwoPointTimedEventPosition_lt_iff_of_sameOrderChamber
        hChamber
        (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1))
        (orderedTwoPointLegEvent (mixedTimeOrderedAtomicLegEquiv τ τ' σ q.1)))
  have hSource (r : d.MixedComponentPosition τ τ' σ B) :
      mixedTimeOrderedAtomicLegPosition τ τ' σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ r.1) = r.1 :=
    mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  have hTarget (r : d.MixedComponentPosition τ τ' σ B) :
      mixedTimeOrderedAtomicLegPosition τ τ' υ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ r.1) =
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B r).1 := by
    rw [← d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B r]
    exact mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv _ _ _ _
  rw [hSource p, hSource q, hTarget p, hTarget q] at hOrder
  exact hOrder

/-- The ambient normalized-pair transport preserves component endpoints up to reversal.
This follows directly from the partner-preserving equivalence of the full pairings. -/
private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_or_swap
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))) ∨
      (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))) := by
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  let f := (mixedTimeAmbientPositionEquiv τ τ' σ).trans
    (mixedTimeAmbientPositionEquiv τ τ' υ).symm
  change (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) = _ ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) = _) ∨
    (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) = _ ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) = _)
  have hpos (p : d.MixedComponentPosition τ τ' σ B) :
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 = f p.1 := by
    apply (mixedTimeAmbientPositionEquiv τ τ' υ).injective
    have h := congrArg Subtype.val
      (show d.mixedComponentPositionEquiv τ τ' υ B
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p) =
        d.mixedComponentPositionEquiv τ τ' σ B p by
        simp [TwoPointDiagram.mixedComponentPositionTimeEquiv])
    change mixedTimeAmbientPositionEquiv τ τ' υ
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeAmbientPositionEquiv τ τ' σ p.1 at h
    simpa [f] using h
  have hPair := d.mixedPairTimeEquiv_pair_eq_or_swap τ τ' σ υ pr.1
  change q.1.1 = (f pr.1.1.1, f pr.1.1.2) ∨
      q.1.1 = (f pr.1.1.2, f pr.1.1.1) at hPair
  have endpoint0 (k : Fin 2)
      (h : q.1.1.1 =
        f (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k)).1) :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k)) := by
    apply Subtype.ext
    change q.1.1.1 = _
    rw [hpos]
    exact h
  have endpoint1 (k : Fin 2)
      (h : q.1.1.2 =
        f (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k)).1) :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k)) := by
    apply Subtype.ext
    change q.1.1.2 = _
    rw [hpos]
    exact h
  rcases hPair with h | h
  · left
    constructor
    · apply endpoint0 0
      simpa only [d.mixedComponentPairEndpointEquiv_apply_val,
        Pairing.pairEndpoint_zero] using congrArg Prod.fst h
    · apply endpoint1 1
      simpa only [d.mixedComponentPairEndpointEquiv_apply_val,
        Pairing.pairEndpoint_one] using congrArg Prod.snd h
  · right
    constructor
    · apply endpoint0 1
      simpa only [d.mixedComponentPairEndpointEquiv_apply_val,
        Pairing.pairEndpoint_one] using congrArg Prod.fst h
    · apply endpoint1 0
      simpa only [d.mixedComponentPairEndpointEquiv_apply_val,
        Pairing.pairEndpoint_zero] using congrArg Prod.snd h

private theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hOrder : ∀ p q : d.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) := by
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  change d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) = _ ∧
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) = _
  rcases d.mixedComponentPairTimeEquiv_endpoints_eq_or_swap τ τ' σ υ B pr with
    hSame | hSwap
  · exact hSame
  · have hSource :
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' σ).mem_pairs_iff pr.1.1.1 pr.1.1.2).mp pr.1.2 |>.1
    have hTransport :=
      (hOrder (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0))
        (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1))).1 hSource
    have hTarget :
        (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1)).1 :=
      ((d.pairingInMixedOrder τ τ' υ).mem_pairs_iff q.1.1.1 q.1.1.2).mp q.1.2 |>.1
    rw [hSwap.1, hSwap.2] at hTarget
    exact (lt_asymm hTarget hTransport).elim

private theorem TwoPointDiagram.mixedComponentCrosses_iff_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hOrder : ∀ p q : d.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1)
    (p q : d.MixedComponentPair τ τ' σ B) :
    Crosses p.1.1 q.1.1 ↔
      Crosses
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B p).1.1
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B q).1.1 := by
  classical
  let tp := d.mixedComponentPairTimeEquiv τ τ' σ υ B p
  let tq := d.mixedComponentPairTimeEquiv τ τ' σ υ B q
  let p0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (p, 0)
  let p1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (p, 1)
  let q0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (q, 0)
  let q1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (q, 1)
  have endpointVals (r : d.MixedComponentPair τ τ' σ B) :
      (d.mixedComponentPairTimeEquiv τ τ' σ υ B r).1.1.1 =
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (r, 0))).1 ∧
        (d.mixedComponentPairTimeEquiv τ τ' σ υ B r).1.1.2 =
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (r, 1))).1 := by
    have hEnds :=
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B hOrder r
    constructor
    · simpa using congrArg Subtype.val hEnds.1
    · simpa using congrArg Subtype.val hEnds.2
  obtain ⟨hp0Val, hp1Val⟩ := endpointVals p
  obtain ⟨hq0Val, hq1Val⟩ := endpointVals q
  have hCross := and_congr (hOrder p0 q0)
    (and_congr (hOrder q0 p1) (hOrder p1 q1))
  rw [← hp0Val, ← hq0Val, ← hp1Val, ← hq1Val] at hCross
  simpa [Crosses, p0, p1, q0, q1] using hCross

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
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  have hEnds := d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder
    τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
      τ τ' σ υ B hChamber) pr
  have hLeg (k : Fin 2) :
      mixedTimeOrderedAtomicLegEquiv τ τ' υ
          (d.mixedComponentPairEndpointEquiv τ τ' υ B (q, k)).1 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k)).1 := by
    have hEndpoint :
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, k) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B
            (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k)) := by
      fin_cases k
      · simpa [q] using hEnds.1
      · simpa [q] using hEnds.2
    rw [hEndpoint]
    exact d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B
      (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, k))
  constructor
  · simpa using hLeg 0
  · simpa using hLeg 1

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
    (fun p q =>
      d.mixedComponentCrosses_iff_of_positionOrder τ τ' σ υ B
        (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
          τ τ' σ υ B hChamber) p q)

end Common
end SecondQuantization
