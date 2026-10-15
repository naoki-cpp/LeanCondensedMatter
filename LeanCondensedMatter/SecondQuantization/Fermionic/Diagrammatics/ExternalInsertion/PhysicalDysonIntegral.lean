import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.PhysicalWickExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity

set_option linter.style.header false

/-!
# Integrated physical mixed-atomic Dyson coefficient

The pointwise free-Gibbs Wick expansion is integrated over the ordered
interaction-time simplex. Chamberwise measurable local boundedness of each
Dyson-signed diagram integrand allows the finite diagram sum to be exchanged
with the integral, without incorrectly assuming global continuity across
external/interaction time crossings.

The operator-side coefficient is defined using the existing mixed-time atomic
field family. Equating that atomic product to a separately constructed
time-ordered product of external fields and quartic interaction operators is
the remaining operator-level step.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Order-n Dyson coefficient of the explicitly mixed-time-ordered atomic
free-Gibbs operator product, including the fermionic atomic-order sign and
the vertex couplings. The Dyson (-1)^n factor is independent of the
mixed-time reordering sign. -/
noncomputable def externalInsertionMixedAtomicDysonCoefficient {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ =>
      (-1 : ℂ) ^ n *
        (externalInsertionMixedAtomicOrderSign externalTime σ *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            (∏ i : Fin n, g (q i)) *
              (freeGibbsDensityOperator ε β).expectation
                (Common.finiteHilbertOperatorAlgEquiv
                  (List.prod (List.ofFn
                    (fun p : Fin (2 * (2 * n + E)) =>
                      timedFieldOperator ε
                        (externalInsertionMixedTimeOrderedAtomicFieldFamily
                          externalLabel externalTime q σ p)))))))

/-- The mixed-atomic free-Gibbs Dyson coefficient equals the existing
integrated fixed-external Wick-diagram coefficient at every perturbative
order. The finite-sum/integral interchange follows from the proved
chamberwise regularity of each diagram's Dyson integrand. -/
theorem externalInsertionMixedAtomicDysonCoefficient_eq_externalInsertionDysonCoefficient
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionMixedAtomicDysonCoefficient
        ε β g externalLabel externalTime n =
      externalInsertionDysonCoefficient
        ε β g externalLabel externalTime n := by
  classical
  have hpoint (σ : Fin n → ℝ) :
      (-1 : ℂ) ^ n *
        (externalInsertionMixedAtomicOrderSign externalTime σ *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            (∏ i : Fin n, g (q i)) *
              (freeGibbsDensityOperator ε β).expectation
                (Common.finiteHilbertOperatorAlgEquiv
                  (List.prod (List.ofFn
                    (fun p : Fin (2 * (2 * n + E)) =>
                      timedFieldOperator ε
                        (externalInsertionMixedTimeOrderedAtomicFieldFamily
                          externalLabel externalTime q σ p)))))) =
        ∑ d : FixedExternalInsertionWickDiagram Mode E n externalLabel,
          d.1.dysonFixedTimeAmplitude ε β g externalTime σ := by
    rw [← sum_fixedExternalInsertionWickDiagram_fixedTimeAmplitude_eq_mixedAtomicExpectation
      ε β g externalLabel externalTime σ]
    rw [Finset.mul_sum]
    rfl
  unfold externalInsertionMixedAtomicDysonCoefficient
  rw [intervalIntegral.orderedSimplexIntegral_congr hpoint]
  rw [intervalIntegral.orderedSimplexIntegral_finsetSum_of_measurableLocallyBounded
    Finset.univ n β
    (fun d : FixedExternalInsertionWickDiagram Mode E n externalLabel =>
      fun σ => d.1.dysonFixedTimeAmplitude ε β g externalTime σ)
    (by
      intro d _
      exact d.1.measurableLocallyBounded_dysonFixedTimeAmplitude
        ε β g externalTime)]
  unfold externalInsertionDysonCoefficient
  apply Finset.sum_congr rfl
  intro d _
  exact d.1.orderedSimplexIntegral_dysonFixedTimeAmplitude
    ε β g externalTime

end Fermionic
end SecondQuantization
