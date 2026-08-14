import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderChamber
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossingTimeLocality
import LeanCondensedMatter.Combinatorics.ListFlatMapOrder

set_option linter.style.header false

/-!
# Mixed component combinatorics on fixed order chambers

Inside one `SameTwoPointOrderChamber`, relative mixed-event order is fixed, and local atomic-leg order
inside each event is fixed. Consequently mixed component position order, pair endpoint transport,
crossings, crossing counts, and statistics weights are chamber-local structural data.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- Complete mixed atomic-leg order is constant inside a common two-point order chamber. -/
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

/-- Component position-time transport preserves strict order inside one chamber. -/
theorem TwoPointDiagram.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ)
    (p q : d.MixedComponentPosition τ τ' σ B) :
    p.1 < q.1 ↔
      (d.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 <
        (d.mixedComponentPositionTimeEquiv τ τ' σ υ B q).1 :=
  d.mixedComponentPositionTimeEquiv_lt_iff_of_legPosition_lt_iff τ τ' σ υ B p q
    (mixedTimeOrderedAtomicLegPosition_lt_iff_of_sameOrderChamber τ τ' σ υ _ _ hChamber)

/-- Pair-time transport preserves normalized endpoint order inside one chamber. -/
theorem TwoPointDiagram.mixedComponentPairTimeEquiv_endpoints_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
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

/-- Component-internal crossings are preserved inside one chamber. -/
theorem TwoPointDiagram.mixedComponentCrossingPreserving_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.MixedComponentCrossingPreserving τ τ' σ υ B :=
  d.mixedComponentCrossingPreserving_of_positionOrder τ τ' σ υ B
    (d.mixedComponentPositionTimeEquiv_lt_iff_of_sameOrderChamber τ τ' σ υ B hChamber)

/-- Component-internal crossing count is constant on one chamber. -/
theorem TwoPointDiagram.mixedComponentCrossingCount_eq_of_sameOrderChamber
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ υ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hChamber : SameTwoPointOrderChamber τ τ' σ υ) :
    d.mixedComponentCrossingCount τ τ' σ B =
      d.mixedComponentCrossingCount τ τ' υ B :=
  d.mixedComponentCrossingCount_eq_of_timeTransport τ τ' σ υ B
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber τ τ' σ υ B hChamber)

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
    (d.mixedComponentCrossingPreserving_of_sameOrderChamber τ τ' σ υ B hChamber)

end Common
end SecondQuantization
