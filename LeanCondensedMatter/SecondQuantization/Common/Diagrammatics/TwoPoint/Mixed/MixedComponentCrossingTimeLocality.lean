import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEndpointTimeTransport
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentTimeTransport

set_option linter.style.header false

/-!
# Component-locality of mixed pair crossings and order chambers

Canonical component pair transport preserves normalized endpoints when component position order is
preserved. Transporting the three inequalities in `Crosses` therefore makes crossing locality a
purely statistics-independent two-point diagram statement. The same transport specializes directly
to fixed mixed-order chambers, where endpoint legs and exchange-statistics weights are constant.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- Preservation of strict mixed order by component position transport implies preservation and
reflection of every crossing between pairs of that component. -/
theorem TwoPointDiagram.mixedComponentCrossingPreserving_of_positionOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hOrder : ∀ p q : d.MixedComponentPosition τ τ' σ B,
      p.1 < q.1 ↔
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1) :
    d.MixedComponentCrossingPreserving τ τ' σ υ B := by
  classical
  intro p q
  let tp := d.mixedComponentPairTimeEquiv τ τ' σ υ B p
  let tq := d.mixedComponentPairTimeEquiv τ τ' σ υ B q
  let p0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (p, 0)
  let p1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (p, 1)
  let q0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (q, 0)
  let q1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (q, 1)
  have hpEnds :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (tp, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0 ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (tp, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1 := by
    simpa [tp, p0, p1] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B hOrder p
  have hqEnds :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (tq, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0 ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (tq, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1 := by
    simpa [tq, q0, q1] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B hOrder q
  have hp0Val :
      tp.1.1.1 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0).1 := by
    simpa [tp] using congrArg Subtype.val hpEnds.1
  have hp1Val :
      tp.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
    simpa [tp] using congrArg Subtype.val hpEnds.2
  have hq0Val :
      tq.1.1.1 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0).1 := by
    simpa [tq] using congrArg Subtype.val hqEnds.1
  have hq1Val :
      tq.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1).1 := by
    simpa [tq] using congrArg Subtype.val hqEnds.2
  have h00 := hOrder p0 q0
  have h01 := hOrder q0 p1
  have h11 := hOrder p1 q1
  unfold Crosses
  constructor
  · rintro ⟨hpq, hqp, hpq'⟩
    have ht00 := h00.mp (by simpa [p0, q0] using hpq)
    have ht01 := h01.mp (by simpa [q0, p1] using hqp)
    have ht11 := h11.mp (by simpa [p1, q1] using hpq')
    refine ⟨?_, ?_, ?_⟩
    · rw [hp0Val, hq0Val]
      exact ht00
    · rw [hq0Val, hp1Val]
      exact ht01
    · rw [hp1Val, hq1Val]
      exact ht11
  · rintro ⟨hpq, hqp, hpq'⟩
    have ht00 :
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0).1 := by
      rw [← hp0Val, ← hq0Val]
      exact hpq
    have ht01 :
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q0).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
      rw [← hq0Val, ← hp1Val]
      exact hqp
    have ht11 :
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 <
          (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q1).1 := by
      rw [← hp1Val, ← hq1Val]
      exact hpq'
    refine ⟨?_, ?_, ?_⟩
    · simpa [p0, q0] using h00.mpr ht00
    · simpa [q0, p1] using h01.mpr ht01
    · simpa [p1, q1] using h11.mpr ht11

/-- Component-local equality of interaction times implies crossing preservation. -/
theorem TwoPointDiagram.mixedComponentCrossingPreserving_of_componentTimeEq
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hTime : d.ComponentTimeEq B σ υ) :
    d.MixedComponentCrossingPreserving τ τ' σ υ B :=
  d.mixedComponentCrossingPreserving_of_positionOrder τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff τ τ' σ υ B hTime)

/-- Inside one order chamber, canonical transport of a normalized component pair preserves the two
underlying standard atomic legs in their normalized order. -/
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpointLegs_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.1 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.1 ∧
      mixedTimeOrderedAtomicLegEquiv τ τ' υ q.1.1.2 =
        mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1.2 := by
  classical
  let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
  let p0 := d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)
  let p1 := d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)
  have hEnds :
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0 ∧
        d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
          d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1 := by
    simpa [q, p0, p1] using
      d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B
        (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
          τ τ' σ υ B hChamber) pr
  have h0Pos :
      q.1.1.1 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p0).1 := by
    simpa [q] using congrArg Subtype.val hEnds.1
  have h1Pos :
      q.1.1.2 = (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p1).1 := by
    simpa [q] using congrArg Subtype.val hEnds.2
  constructor
  · rw [h0Pos]
    simpa [p0] using
      d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p0
  · rw [h1Pos]
    simpa [p1] using
      d.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p1

/-- Component exchange-statistics weight is constant on one chamber. -/
theorem TwoPointDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (s : Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B :=
  d.mixedComponentWeight_eq_of_timeTransport s τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_positionOrder τ τ' σ υ B
      (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
        τ τ' σ υ B hChamber))

end Common
end SecondQuantization
