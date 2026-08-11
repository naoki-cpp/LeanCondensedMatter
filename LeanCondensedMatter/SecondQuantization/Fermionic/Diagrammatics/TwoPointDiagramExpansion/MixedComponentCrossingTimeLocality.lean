import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairEndpointTimeTransport

set_option linter.style.header false

/-!
# Component-locality of mixed pair crossings

Canonical component pair transport preserves each normalized endpoint exactly when the interaction
times agree on that component.  Component position transport also preserves and reflects strict
mixed order under the same hypothesis.  Applying that order equivalence to the three inequalities
that define `Crosses` proves that component-internal fermionic crossings are local to the component's
own interaction times.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- Preservation of strict mixed order by component position transport implies that canonical
pair-time transport preserves and reflects every crossing between pairs of that component:  the three
inequalities defining `Crosses` are transported one by one. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingPreserving_of_positionOrder
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
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

/-- Agreement of interaction times on one full component implies that canonical pair-time transport
preserves and reflects every crossing between pairs of that component. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingPreserving_of_componentTimeEq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hTime : d.ComponentTimeEq B σ υ) :
    d.MixedComponentCrossingPreserving τ τ' σ υ B :=
  d.mixedComponentCrossingPreserving_of_positionOrder τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff τ τ' σ υ B hTime)

end Fermionic
end SecondQuantization
