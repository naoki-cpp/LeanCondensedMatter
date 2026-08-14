import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairProduct
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false

/-!
# Regularity of mixed two-point density-state pair contractions

A fermionic atomic field at imaginary time is an explicit exponential scalar multiplying a bare
creation or annihilation operator. Therefore the canonical free Gibbs density-state contraction of
two fixed field labels has all of its time dependence in two complex exponentials.

This module packages that scalar normal form, lifts it to fixed standard two-point legs, and proves
continuity in the ambient interaction-time assignment. It also identifies the contraction used by a
mixed normalized pair with the corresponding standard-leg contraction. Finite Gibbs coordinate
formulas appear only inside the closed-form proof. No chamber or pair-transport argument is used
here.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Canonical free Gibbs density-state contraction of two time-labelled fermionic fields. -/
noncomputable def timedFieldPairContraction
    (ε : Mode → ℝ) (β : ℝ) (A B : TimedField Mode) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperator
      ((timedFieldOperator ε A).comp (timedFieldOperator ε B)))

/-- Closed form of a density-state pair contraction after extracting the two imaginary-time
exponential factors. -/
theorem timedFieldPairContraction_eq
    (ε : Mode → ℝ) (β : ℝ) (A B : TimedField Mode) :
    timedFieldPairContraction ε β A B =
      Complex.exp (((A.time * externalFieldLabelEnergyShift ε A.label : ℝ) : ℂ)) *
        Complex.exp (((B.time * externalFieldLabelEnergyShift ε B.label : ℝ) : ℂ)) *
          (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperator
              ((bareExternalFieldOperator A.label).comp
                (bareExternalFieldOperator B.label))) := by
  simp only [timedFieldPairContraction,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
  rw [timedFieldOperator_eq_smul, timedFieldOperator_eq_smul,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    Common.finiteGibbsExpectation_smul]

/-- For two fixed field labels, their density-state contraction is jointly continuous in both
imaginary times. -/
theorem continuous_timedFieldPairContraction_times
    (ε : Mode → ℝ) (β : ℝ) (A B : ExternalFieldLabel Mode) :
    Continuous (fun p : ℝ × ℝ =>
      timedFieldPairContraction ε β ⟨p.1, A⟩ ⟨p.2, B⟩) := by
  simp only [timedFieldPairContraction_eq]
  fun_prop

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

omit [Fintype Mode] in
/-- The mixed field family at an atomic position is exactly the descriptor of the fixed standard leg
represented at that position. -/
theorem mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField
    {n : ℕ} (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ p =
      orderedTwoPointLegField i j τ τ' q σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) := by
  let fields := mixedTimeOrderedAtomicFields i j τ τ' q σ
  let legs := mixedTimeOrderedAtomicLegs τ τ' σ
  have hFieldsLen : fields.length = 2 * (2 * n + 1) := by
    exact mixedTimeOrderedAtomicFields_length ε i j τ τ' q σ
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
  change timedFieldOperator ε (mixedTimeOrderedAtomicFieldFamily ε i j τ τ' q σ p) = _
  rw [mixedTimeOrderedAtomicFieldFamily_eq_orderedTwoPointLegField]

omit [LinearOrder Mode] [Fintype Mode] in
/-- The time coordinate of a fixed standard leg varies continuously with the ambient interaction
assignment. -/
theorem continuous_orderedTwoPointLegTime {n : ℕ} (τ τ' : ℝ)
    (leg : OrderedTwoPointLeg n) :
    Continuous (fun σ : Fin n → ℝ => orderedTwoPointLegTime τ τ' σ leg) := by
  cases leg with
  | inl e =>
      change Continuous (fun _ : Fin n → ℝ => twoPointExternalTimes τ τ' e)
      fun_prop
  | inr leg =>
      change Continuous (fun σ : Fin n → ℝ => σ leg.1.1)
      fun_prop

/-- Density-state contraction associated with two fixed standard two-point legs. -/
noncomputable def orderedTwoPointLegPairContraction
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (x y : OrderedTwoPointLeg n) : ℂ :=
  timedFieldPairContraction ε β
    (orderedTwoPointLegField i j τ τ' q σ x)
    (orderedTwoPointLegField i j τ τ' q σ y)

/-- For every fixed pair of standard two-point legs, the density-state contraction is globally
continuous in the ambient interaction-time assignment. -/
theorem continuous_orderedTwoPointLegPairContraction
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (x y : OrderedTwoPointLeg n) :
    Continuous (fun σ : Fin n → ℝ =>
      orderedTwoPointLegPairContraction ε β i j τ τ' q σ x y) := by
  have hTimes : Continuous (fun σ : Fin n → ℝ =>
      (orderedTwoPointLegTime τ τ' σ x, orderedTwoPointLegTime τ τ' σ y)) :=
    (continuous_orderedTwoPointLegTime τ τ' x).prodMk
      (continuous_orderedTwoPointLegTime τ τ' y)
  have hContraction :=
    (continuous_timedFieldPairContraction_times ε β
      (orderedTwoPointLegFieldLabel i j q x)
      (orderedTwoPointLegFieldLabel i j q y)).comp hTimes
  change Continuous
    ((fun p : ℝ × ℝ =>
      timedFieldPairContraction ε β
        ⟨p.1, orderedTwoPointLegFieldLabel i j q x⟩
        ⟨p.2, orderedTwoPointLegFieldLabel i j q y⟩) ∘
      fun σ : Fin n → ℝ =>
        (orderedTwoPointLegTime τ τ' σ x, orderedTwoPointLegTime τ τ' σ y))
  exact hContraction

/-- The contraction used by a normalized mixed pair is the globally continuous density-state
contraction of the two fixed standard legs represented by its endpoints. -/
theorem FixedExternalTwoPointWickDiagram.mixedPairContractionValue_eq_orderedTwoPointLegPairContraction
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (pr : (d.pairingInMixedOrder τ τ' σ).NormalizedPair) :
    d.mixedPairContractionValue ε β τ τ' σ pr =
      orderedTwoPointLegPairContraction ε β i j τ τ' d.vertexLabelSequence σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.1)
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ pr.1.2) := by
  unfold FixedExternalTwoPointWickDiagram.mixedPairContractionValue
    mixedTimeOrderedAtomicPairValue orderedTwoPointLegPairContraction timedFieldPairContraction
  rw [mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegField,
    mixedTimeOrderedAtomicOperatorFamily_eq_orderedTwoPointLegField]

end Fermionic
end SecondQuantization
