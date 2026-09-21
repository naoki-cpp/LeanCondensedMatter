import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction

set_option linter.style.header false

/-!
# Mixed two-point density-state pair contractions

A fermionic atomic field at imaginary time is an explicit exponential scalar multiplying a bare
creation or annihilation operator. This module owns the two-point semantic pair-contraction API: fixed standard-leg descriptors and
transport between mixed-order pairs and standard two-point legs. The representation-independent
free-Gibbs contraction of time-labelled fields is owned by `Fermionic.Thermal`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The field label carried by one fixed standard two-point leg. -/
def orderedTwoPointLegFieldLabel {n : ℕ} (i j : Mode)
    (q : Fin n → QuarticVertexLabel Mode) :
    OrderedTwoPointLeg n → ExternalFieldLabel Mode
  | .inl e => twoPointExternalLabels i j e
  | .inr leg => quarticLocalLegExternalFieldLabel (q leg.1.1) leg.2

/-- The imaginary time carried by one fixed standard two-point leg. -/
def orderedTwoPointLegTime {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    OrderedTwoPointLeg n → ℝ
  | .inl e => twoPointExternalTimes τ τ' e
  | .inr leg => σ leg.1.1

/-- Time-labelled field descriptor carried by one fixed standard two-point leg. -/
def orderedTwoPointLegField {n : ℕ} (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (leg : OrderedTwoPointLeg n) : TimedField Mode :=
  ⟨orderedTwoPointLegTime τ τ' σ leg,
    orderedTwoPointLegFieldLabel i j q leg⟩

omit [LinearOrder Mode] [Fintype Mode] in
private theorem map_orderedTwoPointLegField_twoPointTimedEventAtomicLegs
    {n : ℕ} (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicLegs event).map
        (orderedTwoPointLegField i j τ τ' q σ) =
      twoPointTimedEventAtomicFields i j τ τ' q σ event := by
  cases event with
  | inl e =>
      simp [twoPointTimedEventAtomicLegs, twoPointTimedEventAtomicFields,
        orderedTwoPointLegField, orderedTwoPointLegTime, orderedTwoPointLegFieldLabel]
  | inr v =>
      simp [twoPointTimedEventAtomicLegs, twoPointTimedEventAtomicFields,
        orderedTwoPointLegField, orderedTwoPointLegTime, orderedTwoPointLegFieldLabel]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem map_orderedTwoPointLegField_mixedTimeOrderedAtomicLegs
    {n : ℕ} (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (mixedTimeOrderedAtomicLegs τ τ' σ).map
        (orderedTwoPointLegField i j τ τ' q σ) =
      mixedTimeOrderedAtomicFields i j τ τ' q σ := by
  unfold mixedTimeOrderedAtomicLegs mixedTimeOrderedAtomicFields
  let events := orderedTwoPointTimedEvents τ τ' σ
  change (events.flatMap twoPointTimedEventAtomicLegs).map
      (orderedTwoPointLegField i j τ τ' q σ) =
    events.flatMap (twoPointTimedEventAtomicFields i j τ τ' q σ)
  induction events with
  | nil => rfl
  | cons event events ih =>
      rw [List.flatMap_cons, List.map_append, List.flatMap_cons,
        map_orderedTwoPointLegField_twoPointTimedEventAtomicLegs, ih]

omit [LinearOrder Mode] [Fintype Mode] in
/-- The mixed field family at an atomic position is exactly the descriptor of the fixed standard leg
represented at that position. -/
theorem mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField
    {n : ℕ} (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p =
      orderedTwoPointLegField i j τ τ' q σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) := by
  let fields := mixedTimeOrderedAtomicFields i j τ τ' q σ
  let legs := mixedTimeOrderedAtomicLegs τ τ' σ
  have hFieldsLen : fields.length = 2 * (2 * n + 1) := by
    exact mixedTimeOrderedAtomicFields_length i j τ τ' q σ
  have hLegsLen : legs.length = 2 * (2 * n + 1) := by
    exact mixedTimeOrderedAtomicLegs_length τ τ' σ
  have hpFields : p.1 < fields.length := by
    rw [hFieldsLen]
    exact p.2
  have hpLegs : p.1 < legs.length := by
    rw [hLegsLen]
    exact p.2
  have hMaps :
      fields = legs.map (orderedTwoPointLegField i j τ τ' q σ) := by
    exact (map_orderedTwoPointLegField_mixedTimeOrderedAtomicLegs i j τ τ' q σ).symm
  have hMappedAt :
      fields[p.1]'hpFields =
        (legs.map (orderedTwoPointLegField i j τ τ' q σ))[p.1]'(by
          simpa using hpLegs) := by
    have hOpt := congrArg (fun xs => xs[p.1]?) hMaps
    simpa [hpFields, hpLegs] using hOpt
  change fields[p.1]'hpFields = _
  calc
    fields[p.1]'hpFields =
        (legs.map (orderedTwoPointLegField i j τ τ' q σ))[p.1]'(by
          simpa using hpLegs) := hMappedAt
    _ = orderedTwoPointLegField i j τ τ' q σ (legs[p.1]'hpLegs) :=
      (List.getElem_map_rev (orderedTwoPointLegField i j τ τ' q σ)).symm
    _ = orderedTwoPointLegField i j τ τ' q σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) := by
      rfl

omit [Fintype Mode] in
/-- Operator form of `mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField`. -/
theorem mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegField
    {n : ℕ} (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ p =
      timedFieldOperator ε
        (orderedTwoPointLegField i j τ τ' q σ
          (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)) := by
  change timedFieldOperator ε (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p) = _
  rw [mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField]

/-- Density-state contraction associated with two fixed standard two-point legs. -/
noncomputable def orderedTwoPointLegPairContraction
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (x y : OrderedTwoPointLeg n) : ℂ :=
  timedFieldPairContraction ε β
    (orderedTwoPointLegField i j τ τ' q σ x)
    (orderedTwoPointLegField i j τ τ' q σ y)

/-- Canonical free Gibbs density-state contraction attached to one normalized pair in the actual
mixed-time pairing. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.1.pairingInMixedOrder τ τ' σ).NormalizedPair) : ℂ :=
  mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ d.vertexLabelSequence
    pr.1.1 pr.1.2

/-- The contraction used by a normalized mixed pair is the density-state contraction of the two
fixed standard legs represented by its endpoints. -/
theorem FixedExternalTwoPointWickDiagram.mixedPairContractionValue_eq_orderedTwoPointLegPairContraction
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.1.pairingInMixedOrder τ τ' σ).NormalizedPair) :
    d.mixedPairContractionValue ε β τ τ' σ pr =
      orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1)
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.2) := by
  unfold FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    mixedTimeOrderedAtomicPairValue orderedTwoPointLegPairContraction timedFieldPairContraction
    freeGibbsPairContraction
  rw [mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegField,
    mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegField]

end Fermionic
end SecondQuantization
