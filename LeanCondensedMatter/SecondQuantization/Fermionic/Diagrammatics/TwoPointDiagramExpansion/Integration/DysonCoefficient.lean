import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.InteractionPictureVertexDyson

set_option linter.style.header false

/-!
# Ordered-simplex two-point Dyson coefficients

This module integrates the fixed-time external-leg Wick expansion over the ordered simplex and
attaches the `(-1)^n` Dyson sign. The operator coefficient now uses the generic
finite Gibbs expectation at explicit chemical potential μ, while imaginary-time operators
continue to evolve under the physical free dispersion ε.

The unconditional public theorem integrates the pointwise finite sum over diagrams.  Commuting that
finite diagram sum with the ordered-simplex integral is a separate analytic obligation, because
mixed time ordering changes when an interaction time crosses an external time and no individual
diagram amplitude is continuous.  It is discharged under measurable local boundedness in
`DiagramSumIntegral.lean` by `twoPointDiagramCoefficient_eq_sum_dysonAmplitude`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- At explicit chemical potential μ, the mixed event-level finite Gibbs expectation
equals the external-order sign times the grand-canonical pairing sum. Physical
time-labelled fields evolve with ε, while their Gibbs weight uses ε - μ. -/
theorem finiteGibbsExpectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue
    {n : ℕ} (ε : Mode → ℝ) (β μ : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    Common.finiteGibbsExpectation (fermionEnergy (fun k => ε k - μ)) β
        (mixedTimeOrderedVertexComp ε i j τ τ' q σ) =
      twoPointExternalOrderSign τ τ' *
        ∑ pairing : Pairing (2 * n + 1),
          pairing.evaluation (pairing.weight Common.Statistics.fermion)
            (fun a b => grandCanonicalTimedFieldPairContraction ε β μ
              (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ a)
              (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ b)) := by
  rw [mixedTimeOrderedVertexComp_eq_prod_atomicOperators,
    Common.finiteGibbsExpectation, map_smul, smul_eq_mul]
  have hwick :=
    grandCanonicalGibbsExpectation_prod_timedFieldOperator_eq_sum_pairing
      ε β μ (2 * n + 1) (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ)
  have hpair (A B : TimedField Mode) :
      Common.finiteGibbsExpectation (fermionEnergy (fun k => ε k - μ)) β
        ((timedFieldOperator ε A).comp (timedFieldOperator ε B)) =
      grandCanonicalTimedFieldPairContraction ε β μ A B := rfl
  simp_rw [hpair] at hwick
  change Common.finiteGibbsExpectation (fermionEnergy (fun k => ε k - μ)) β
    (List.prod (List.ofFn (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ))) = _ at hwick
  have hfields :
      List.ofFn (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ) =
        mixedTimeOrderedAtomicFields i j τ τ' q σ := by
    let fields := mixedTimeOrderedAtomicFields i j τ τ' q σ
    have h : fields.length = 2 * (2 * n + 1) :=
      mixedTimeOrderedAtomicFields_length i j τ τ' q σ
    simpa [mixedTimeOrderedAtomicFieldFamily, fields] using
      (List.ofFn_congr h fields.get).symm.trans (List.ofFn_get fields)
  have hoperators :
      List.ofFn (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ) =
        mixedTimeOrderedAtomicOperators ε i j τ τ' q σ := by
    change List.ofFn (fun p => timedFieldOperator ε
      (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p)) = _
    rw [List.ofFn_comp', hfields]
    simp only [mixedTimeOrderedAtomicFields, mixedTimeOrderedAtomicOperators, List.map_flatMap]
    have hmap (event : TwoPointTimedEvent n) :
        (twoPointTimedEventAtomicFields i j τ τ' q σ event).map (timedFieldOperator ε) =
          twoPointTimedEventAtomicOperators ε i j τ τ' q σ event := by
      cases event with
      | inl e =>
          simp [twoPointTimedEventAtomicFields, timedFieldOperator,
            twoPointTimedEventAtomicOperators]
      | inr v =>
          rw [twoPointTimedEventAtomicFields, twoPointTimedEventAtomicOperators_interaction,
            List.map_ofFn]
          exact congrArg List.ofFn (funext fun l => by
            simpa [Function.comp_def, quarticLocalLegOperator,
              Common.quarticLocalLegOperator] using
              timedFieldOperator_quarticLocalLeg ε (σ v) (Common.quarticLocalLeg (q v) l))
    simp_rw [hmap]
  rw [hoperators] at hwick
  simp only [Common.finiteGibbsExpectation] at hwick
  rw [hwick]

/-- Order-`n` perturbative two-point coefficient at explicit chemical potential μ.
The finite Gibbs weight uses ε - μ, while the physical vertex and external-field
imaginary-time evolution uses ε. -/
noncomputable def twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (fun σ =>
      ∑ q : Fin n → QuarticVertexLabel Mode,
        orderedTwoPointVertexWeight g q *
          Common.finiteGibbsExpectation (fermionEnergy (fun k => ε k - μ)) β
            (mixedTimeOrderedVertexComp ε i j τ τ' q σ))

/-- The general atomic-order sign specializes to the two-point external-field
exchange sign, independently of the interaction times. -/
theorem externalInsertionMixedAtomicOrderSign_twoPoint
    {n : ℕ} (τ τ' : ℝ) (σ : Fin n → ℝ) :
    externalInsertionMixedAtomicOrderSign (E := 1) (twoPointExternalTimes τ τ') σ =
      twoPointExternalOrderSign τ τ' := by
  classical
  rw [externalInsertionMixedAtomicOrderSign,
    externalInsertionStandardToMixedAtomicPositionEquiv_sign_twoPoint]
  by_cases h : τ < τ'
  · simp [h, twoPointExternalOrderSign, Common.Statistics.zetaInt]
  · simp [h, twoPointExternalOrderSign]

omit [Fintype Mode] in
/-- The two physical mixed vertex products coincide, including at equal times.
Both definitions use the same event operators and the same stable order. -/
theorem mixedTimeOrderedVertexComp_eq_externalInsertion
    {n : ℕ} (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    mixedTimeOrderedVertexComp ε i j τ τ' q σ =
      externalInsertionMixedTimeOrderedVertexComp (E := 1) ε
        (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') q σ := by
  simp only [mixedTimeOrderedVertexComp, externalInsertionMixedTimeOrderedVertexComp,
    orderedTwoPointTimedEvents_eq_externalInsertion,
    externalInsertionMixedAtomicOrderSign_twoPoint, twoPointTimedEventOperator]

/-- The physical two-point Dyson coefficient is the two-external specialization
of the general vertex Dyson coefficient at arbitrary real μ and β. -/
theorem twoPointDysonCoefficient_eq_externalInsertionVertexDysonCoefficient
    {n : ℕ} (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDysonCoefficient (n := n) ε β μ g i j τ τ' =
      externalInsertionVertexDysonCoefficient (E := 1) ε β μ g
        (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') n := by
  unfold twoPointDysonCoefficient externalInsertionVertexDysonCoefficient
  rw [← intervalIntegral.orderedSimplexIntegral_smul]
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  simp only [mixedTimeOrderedVertexComp_eq_externalInsertion, orderedTwoPointVertexWeight]

/-- At every perturbative order, the physical-H explicit-μ two-point
coefficient equals its effective-dispersion zero-μ coefficient times the
external-field factor. No sign or positivity assumption on μ or β is needed. -/
theorem twoPointDysonCoefficient_eq_shiftedDispersion {n : ℕ}
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDysonCoefficient (n := n) ε β μ g i j τ τ' =
      twoPointChemicalPotentialFactor μ τ τ' *
        twoPointDysonCoefficient (n := n) (fun k => ε k - μ) β 0 g i j τ τ' := by
  unfold twoPointDysonCoefficient
  simp only [sub_zero]
  rw [mul_left_comm (twoPointChemicalPotentialFactor μ τ τ') ((-1 : ℂ) ^ n)]
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  rw [← intervalIntegral.orderedSimplexIntegral_smul]
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [mixedTimeOrderedVertexComp_eq_shiftedDispersion ε μ]
  simp only [Common.finiteGibbsExpectation, map_smul, smul_eq_mul]
  ring

/-- The ordered-simplex external-leg diagram coefficient equals the mixed time-ordered Dyson
coefficient at every perturbation order. -/
theorem twoPointDiagramCoefficient_eq_twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient (n := n) ε β g i j τ τ' =
      twoPointDysonCoefficient (n := n) ε β 0 g i j τ τ' := by
  unfold twoPointDiagramCoefficient twoPointDysonCoefficient
  simp only [sub_zero]
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  unfold twoPointDiagramIntegrand
  have hsum :
      (∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
          d.fixedTimeAmplitude ε β g τ τ' σ) =
        twoPointExternalOrderSign τ τ' *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            orderedTwoPointVertexWeight g q *
              ∑ pairing : Pairing (2 * n + 1),
                orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
    calc
      (∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
          d.fixedTimeAmplitude ε β g τ τ' σ) =
        ∑ x : OrderedTwoPointWickDiagramData Mode n,
          orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ x := by
        simpa [FixedExternalTwoPointWickDiagram.fixedTimeAmplitude] using
          (Equiv.sum_comp
            (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ)
            (orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ))
      _ = ∑ q : Fin n → QuarticVertexLabel Mode,
          ∑ pairing : Pairing (2 * n + 1),
            orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ (q, pairing) :=
        Fintype.sum_prod_type _
      _ = ∑ q : Fin n → QuarticVertexLabel Mode,
          (twoPointExternalOrderSign τ τ' * orderedTwoPointVertexWeight g q) *
            ∑ pairing : Pairing (2 * n + 1),
              orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro pairing _
        rfl
      _ = twoPointExternalOrderSign τ τ' *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            orderedTwoPointVertexWeight g q *
              ∑ pairing : Pairing (2 * n + 1),
                orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hpoint :=
    finiteGibbsExpectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue
      ε β 0 i j τ τ' q σ
  simp only [sub_zero] at hpoint
  rw [hpoint]
  have hkernel :
      mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ q =
        (fun a b => grandCanonicalTimedFieldPairContraction ε β 0
          (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ a)
          (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ b)) := rfl
  simp only [orderedTwoPointPairingValue, hkernel]
  ring

end Fermionic
end SecondQuantization
