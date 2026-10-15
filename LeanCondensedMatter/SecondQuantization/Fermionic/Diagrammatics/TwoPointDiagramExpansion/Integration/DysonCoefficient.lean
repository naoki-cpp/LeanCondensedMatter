import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false

/-!
# Ordered-simplex two-point Dyson coefficients

This module integrates the fixed-time external-leg Wick expansion over the ordered simplex and
attaches the `(-1)^n` Dyson sign. The operator presentation uses the canonical free Gibbs density
state directly; no parallel finite-Gibbs coefficient API is maintained.

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

omit [Fintype Mode] in
/-- Mapping one event's field descriptors to operators recovers its atomic operator list. -/
private theorem map_timedFieldOperator_twoPointTimedEventAtomicFields {n : ℕ}
    (ε : Mode → ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ)
    (event : TwoPointTimedEvent n) :
    (twoPointTimedEventAtomicFields i j τ τ' q σ event).map (timedFieldOperator ε) =
      twoPointTimedEventAtomicOperators ε i j τ τ' q σ event := by
  cases event with
  | inl e =>
      simp [twoPointTimedEventAtomicFields, timedFieldOperator, twoPointTimedEventAtomicOperators]
  | inr v =>
      rw [twoPointTimedEventAtomicFields, twoPointTimedEventAtomicOperators_interaction,
        List.map_ofFn]
      exact congrArg List.ofFn (funext fun l => by
        simpa [Function.comp_def, quarticLocalLegOperator, Common.quarticLocalLegOperator] using
          timedFieldOperator_quarticLocalLeg ε (σ v) (Common.quarticLocalLeg (q v) l))

/-- The mixed event-level density-state expectation is the external-order sign times the sum of
canonical pairing evaluations. -/
theorem freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv (mixedTimeOrderedVertexComp ε i j τ τ' q σ)) =
      twoPointExternalOrderSign τ τ' *
        ∑ pairing : Pairing (2 * n + 1),
          orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    mixedTimeOrderedVertexComp_eq_prod_atomicOperators,
    Common.finiteGibbsExpectation_smul]
  have hwick :=
    freeGibbsDensityOperator_expectation_prod_timedFieldOperator_eq_sum_pairing
      ε β (2 * n + 1) (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ)
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] at hwick
  change Common.finiteGibbsExpectation (fermionEnergy ε) β
    (List.prod (List.ofFn (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ))) = _ at hwick
  have hfields :
      List.ofFn (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ) =
        mixedTimeOrderedAtomicFields i j τ τ' q σ := by
    let fields := mixedTimeOrderedAtomicFields i j τ τ' q σ
    simpa only [mixedTimeOrderedAtomicFieldFamily, fields] using
      (List.ofFn_congr (mixedTimeOrderedAtomicFields_length i j τ τ' q σ)
        fields.get).symm.trans (List.ofFn_get fields)
  have hoperators :
      List.ofFn (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ) =
        mixedTimeOrderedAtomicOperators ε i j τ τ' q σ := by
    change List.ofFn (fun p => timedFieldOperator ε
      (mixedTimeOrderedAtomicFieldFamily i j τ τ' q σ p)) = _
    rw [List.ofFn_comp', hfields]
    simp only [mixedTimeOrderedAtomicFields, mixedTimeOrderedAtomicOperators, List.map_flatMap]
    simp_rw [map_timedFieldOperator_twoPointTimedEventAtomicFields]
  rw [hoperators] at hwick
  rw [hwick]
  rfl

/-- The canonical order-`n` perturbative two-point coefficient in the density-state operator
presentation. -/
noncomputable def twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  (-1 : ℂ) ^ n * intervalIntegral.orderedSimplexIntegral n β
    (fun σ =>
      ∑ q : Fin n → QuarticVertexLabel Mode,
        orderedTwoPointVertexWeight g q *
          (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperatorAlgEquiv
              (mixedTimeOrderedVertexComp ε i j τ τ' q σ)))

/-- The ordered-simplex external-leg diagram coefficient equals the mixed time-ordered Dyson
coefficient at every perturbation order. -/
theorem twoPointDiagramCoefficient_eq_twoPointDysonCoefficient {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramCoefficient (n := n) ε β g i j τ τ' =
      twoPointDysonCoefficient (n := n) ε β g i j τ τ' := by
  unfold twoPointDiagramCoefficient twoPointDysonCoefficient
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
  rw [freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue]
  ring

end Fermionic
end SecondQuantization
