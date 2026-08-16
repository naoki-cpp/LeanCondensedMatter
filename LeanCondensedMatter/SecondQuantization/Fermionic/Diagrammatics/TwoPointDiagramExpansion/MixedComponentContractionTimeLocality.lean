import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentCrossingTimeLocality
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairTimeTransport

set_option linter.style.header false

/-!
# Component-locality of mixed density-state contractions

Common component-position time transport preserves the standard leg and supporting event time. This
module uses that structural fact to show that the fermionic atomic operators and free-Gibbs pair
contractions are local to the interaction times of their own component.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode]

private noncomputable def orderedTwoPointLegOperator {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    OrderedTwoPointLeg n → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
  | .inl e =>
      externalFieldOperator ε (twoPointExternalTimes τ τ' e) (twoPointExternalLabels i j e)
  | .inr leg =>
      imaginaryTimeEvolve ε (σ leg.1.1)
        (quarticLocalLegOperator (q leg.1.1) leg.2)

private theorem map_orderedTwoPointLegOperator_twoPointTimedEventAtomicLegs
    {n : ℕ} (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicLegs event).map
        (orderedTwoPointLegOperator ε i j τ τ' q σ) =
      twoPointTimedEventAtomicOperators ε i j τ τ' q σ event := by
  cases event with
  | inl e => simp [twoPointTimedEventAtomicLegs, orderedTwoPointLegOperator]
  | inr v => simp [twoPointTimedEventAtomicLegs, orderedTwoPointLegOperator]

private theorem map_orderedTwoPointLegOperator_mixedTimeOrderedAtomicLegs
    {n : ℕ} (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicLegs τ τ' σ).map
        (orderedTwoPointLegOperator ε i j τ τ' q σ) =
      mixedTimeOrderedAtomicOperators ε i j τ τ' q σ := by
  unfold mixedTimeOrderedAtomicLegs mixedTimeOrderedAtomicOperators
  let events := orderedTwoPointTimedEvents τ τ' σ
  change (events.flatMap twoPointTimedEventAtomicLegs).map
      (orderedTwoPointLegOperator ε i j τ τ' q σ) =
    events.flatMap (twoPointTimedEventAtomicOperators ε i j τ τ' q σ)
  induction events with
  | nil => rfl
  | cons event events ih =>
      rw [List.flatMap_cons, List.map_append, List.flatMap_cons,
        map_orderedTwoPointLegOperator_twoPointTimedEventAtomicLegs, ih]

private theorem mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegOperator
    {n : ℕ} (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ p =
      orderedTwoPointLegOperator ε i j τ τ' q σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) := by
  let fields := mixedTimeOrderedAtomicFields i j τ τ' q σ
  let legs := mixedTimeOrderedAtomicLegs τ τ' σ
  have hFieldsLen : fields.length = 2 * (2 * n + 1) :=
    mixedTimeOrderedAtomicFields_length ε i j τ τ' q σ
  have hLegsLen : legs.length = 2 * (2 * n + 1) :=
    mixedTimeOrderedAtomicLegs_length τ τ' σ
  have hpFields : p.1 < fields.length := by rw [hFieldsLen]; exact p.2
  have hpLegs : p.1 < legs.length := by rw [hLegsLen]; exact p.2
  have hMaps :
      fields.map (timedFieldOperator ε) =
        legs.map (orderedTwoPointLegOperator ε i j τ τ' q σ) := by
    calc
      fields.map (timedFieldOperator ε) =
          mixedTimeOrderedAtomicOperators ε i j τ τ' q σ :=
        map_timedFieldOperator_mixedTimeOrderedAtomicFields ε i j τ τ' q σ
      _ = legs.map (orderedTwoPointLegOperator ε i j τ τ' q σ) :=
        (map_orderedTwoPointLegOperator_mixedTimeOrderedAtomicLegs ε i j τ τ' q σ).symm
  have hMappedAt :
      (fields.map (timedFieldOperator ε))[p.1]'(by simpa using hpFields) =
        (legs.map (orderedTwoPointLegOperator ε i j τ τ' q σ))[p.1]'(by
          simpa using hpLegs) := by
    have hOpt := congrArg (fun xs => xs[p.1]?) hMaps
    simpa [hpFields, hpLegs] using hOpt
  change timedFieldOperator ε (fields[p.1]'hpFields) = _
  calc
    timedFieldOperator ε (fields[p.1]'hpFields) =
        (fields.map (timedFieldOperator ε))[p.1]'(by simpa using hpFields) :=
      List.getElem_map_rev (timedFieldOperator ε)
    _ = (legs.map (orderedTwoPointLegOperator ε i j τ τ' q σ))[p.1]'(by
          simpa using hpLegs) := hMappedAt
    _ = orderedTwoPointLegOperator ε i j τ τ' q σ (legs[p.1]'hpLegs) :=
      (List.getElem_map_rev (orderedTwoPointLegOperator ε i j τ τ' q σ)).symm
    _ = orderedTwoPointLegOperator ε i j τ τ' q σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) := by rfl

/-- Component-position time transport preserves the represented atomic operator whenever the two
interaction-time assignments agree on that component. -/
private theorem mixedTimeOrderedAtomicOperatorFamily_positionTimeEquiv
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hTime : d.1.ComponentTimeEq B σ υ)
    (p : d.1.MixedComponentPosition τ τ' σ B) :
    mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence υ
        (d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p).1 =
      mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence σ p.1 := by
  rw [mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegOperator,
    mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegOperator,
    d.1.mixedTimeOrderedAtomicLegEquiv_positionTimeEquiv τ τ' σ υ B p]
  have hEventTime := d.1.componentPosition_eventTime_eq τ τ' σ υ B hTime p
  generalize hleg : mixedTimeOrderedAtomicLegEquiv τ τ' σ p.1 = leg at hEventTime ⊢
  cases leg with
  | inl e => rfl
  | inr leg =>
      rcases leg with ⟨v, l⟩
      have hv : σ v.1 = υ v.1 := by
        simpa [orderedTwoPointLegEvent, twoPointTimedEventTime] using hEventTime
      simp only [orderedTwoPointLegOperator]
      rw [← hv]

section GibbsContractions

variable [Fintype Mode]

/-- Component-local equality of interaction times preserves the canonical density-state contraction
attached to one normalized pair under canonical pair-time transport. -/
private theorem mixedPairContractionValue_eq_of_componentTimeEq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hTime : d.1.ComponentTimeEq B σ υ)
    (p : d.1.MixedComponentPair τ τ' σ B) :
    d.mixedPairContractionValue ε β τ τ' σ p.1 =
      d.mixedPairContractionValue ε β τ τ' υ
        (d.1.mixedComponentPairTimeEquiv τ τ' σ υ B p).1 := by
  let tp := d.1.mixedComponentPairTimeEquiv τ τ' σ υ B p
  let p0 := d.1.mixedComponentPairEndpointEquiv τ τ' σ B (p, 0)
  let p1 := d.1.mixedComponentPairEndpointEquiv τ τ' σ B (p, 1)
  have hEnds :
      d.1.mixedComponentPairEndpointEquiv τ τ' υ B (tp, 0) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p0 ∧
        d.1.mixedComponentPairEndpointEquiv τ τ' υ B (tp, 1) =
          d.1.mixedComponentPositionTimeEquiv τ τ' σ υ B p1 := by
    simpa [tp, p0, p1] using
      d.1.mixedComponentPairTimeEquiv_endpoints_eq τ τ' σ υ B hTime p
  have hOp0 :=
    mixedTimeOrderedAtomicOperatorFamily_positionTimeEquiv d ε τ τ' σ υ B hTime p0
  have hOp1 :=
    mixedTimeOrderedAtomicOperatorFamily_positionTimeEquiv d ε τ τ' σ υ B hTime p1
  rw [← hEnds.1] at hOp0
  rw [← hEnds.2] at hOp1
  have hEndpoint0 :
      mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence σ p.1.1.1 =
        mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence υ tp.1.1.1 := by
    simpa [p0, tp] using hOp0.symm
  have hEndpoint1 :
      mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence σ p.1.1.2 =
        mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' d.vertexLabelSequence υ tp.1.1.2 := by
    simpa [p1, tp] using hOp1.symm
  unfold FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    mixedTimeOrderedAtomicPairValue
  rw [hEndpoint0, hEndpoint1]

/-- The complete mixed component pairing value depends only on the interaction times of that
component. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairingValue_eq_of_componentTimeEq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ υ : Fin n → ℝ)
    (B : d.1.componentPartition.parts) (hTime : d.1.ComponentTimeEq B σ υ) :
    d.mixedComponentPairingValue ε β τ τ' σ B =
      d.mixedComponentPairingValue ε β τ τ' υ B :=
  d.mixedComponentPairingValue_eq_of_timeTransport ε β τ τ' σ υ B
    (d.1.mixedComponentCrossingPreserving_of_componentTimeEq τ τ' σ υ B hTime)
    (fun p => mixedPairContractionValue_eq_of_componentTimeEq d ε β τ τ' σ υ B hTime p)

end GibbsContractions

end Fermionic
end SecondQuantization
