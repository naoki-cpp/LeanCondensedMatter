import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedOrderChamber
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossingTimeLocality
import LeanCondensedMatter.Combinatorics.ListFlatMapOrder

set_option linter.style.header false

/-!
# Mixed component combinatorics on fixed order chambers

Inside one `SameTwoPointOrderChamber`, the relative order of distinct mixed events is fixed.  The
relative order of atomic legs belonging to one event is fixed by that event's local leg list.  Thus
the complete mixed atomic-leg order is constant on a chamber even though the actual interaction
times may vary.

This module lifts that statement through the existing component position and normalized-pair time
transports.  In particular, pair normalization cannot swap endpoints inside one chamber, and the
component-internal fermionic crossing relation is preserved without requiring `ComponentTimeEq`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- The complete mixed atomic-leg order is constant inside one mixed-event order chamber.  Distinct
event blocks use chamber invariance of event positions; legs in one event block use the fixed local
leg order. -/
theorem mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber {n : ℕ}
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (x y : OrderedTwoPointLeg n)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    (mixedTimeOrderedAtomicLegPosition τ τ' σ x <
        mixedTimeOrderedAtomicLegPosition τ τ' σ y) ↔
      (mixedTimeOrderedAtomicLegPosition τ τ' υ x <
        mixedTimeOrderedAtomicLegPosition τ τ' υ y) :=
  mixedTimeOrderedAtomicLegPosition_lt_iff_of_eventPosition_lt_iff τ τ' σ υ x y
    (orderedTwoPointTimedEventPosition_lt_iff_of_sameOrderChamber
      hChamber (orderedTwoPointLegEvent x) (orderedTwoPointLegEvent y))

/-- Canonical transport of positions belonging to one full component preserves strict mixed order
throughout one order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 :=
  d.mixedComponentPositionTimeEquiv_lt_iff_of_legPosition_lt_iff τ τ' σ υ B p q
    (mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber τ τ' σ υ _ _ hChamber)

/-- Inside one order chamber, canonical pair-time transport preserves the normalized endpoint order
exactly; the swap alternative cannot occur even though the component interaction times may change. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (pr : d.MixedComponentPair τ τ' σ B) :
    let q := d.mixedComponentPairTimeEquiv τ τ' σ υ B pr
    d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 0) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 0)) ∧
      d.mixedComponentPairEndpointEquiv τ τ' υ B (q, 1) =
        d.mixedComponentPositionTimeEquiv τ τ' σ υ B
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (pr, 1)) :=
  d.mixedComponentPairTimeEquiv_endpoints_eq_of_positionOrder τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber τ τ' σ υ B hChamber) pr

/-- Canonical component pair transport preserves and reflects every component-internal crossing
inside one mixed-event order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingPreserving_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.MixedComponentCrossingPreserving τ τ' σ υ B :=
  d.mixedComponentCrossingPreserving_of_positionOrder τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber τ τ' σ υ B hChamber)

/-- The number of component-internal crossings is constant on one mixed-event order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentCrossingCount_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentCrossingCount τ τ' σ B =
      d.mixedComponentCrossingCount τ τ' υ B :=
  d.mixedComponentCrossingCount_eq_of_timeTransport τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber
      τ τ' σ υ B hChamber)

/-- The exchange-statistics weight of one component is constant on one mixed-event order chamber. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentWeight_eq_of_sameOrderChamber
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (s : Common.Statistics) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentWeight s τ τ' σ B =
      d.mixedComponentWeight s τ τ' υ B :=
  d.mixedComponentWeight_eq_of_timeTransport s τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber
      τ τ' σ υ B hChamber)

end Fermionic
end SecondQuantization
