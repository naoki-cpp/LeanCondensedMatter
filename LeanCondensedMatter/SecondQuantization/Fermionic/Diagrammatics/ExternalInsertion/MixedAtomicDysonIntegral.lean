import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.FreeGibbsWickExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.DiagramRegularity

set_option linter.style.header false

/-!
# Integrated free-Gibbs mixed-atomic Dyson coefficient

The pointwise free-Gibbs Wick-pairing identity is integrated over the ordered
interaction-time simplex. Chamberwise measurable local boundedness of each
Dyson-signed diagram integrand allows the finite diagram sum to be exchanged
with the integral, without incorrectly assuming global continuity across
external/interaction time crossings.

The operator-side coefficient is defined using the existing mixed-time atomic
field family. The equality with the time-ordered product of full
interaction-picture quartic vertices and external fields is established in
`InteractionPictureVertexDyson`, downstream of this module. The physical vertex
product is owned by the imaginary-time layer; its integrated coefficient
is defined here independently of the vacuum Cauchy decomposition.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Order-n Dyson coefficient of full interaction-picture quartic
vertices inserted among a fixed family of external fermionic fields.

The Gibbs state is the normalized grand-canonical finite Gibbs expectation
with explicit μ; physical imaginary-time evolution remains at ε. The Dyson (-1)^n
factor is distinct from the fermionic mixed-time ordering sign. -/
noncomputable def externalInsertionVertexDysonCoefficient {E : ℕ}
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ => (-1 : ℂ) ^ n *
      ∑ q : Fin n → QuarticVertexLabel Mode,
        (∏ i : Fin n, g (q i)) *
          Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
            (externalInsertionMixedTimeOrderedVertexComp
              ε externalLabel externalTime q σ))

/-- Physical-H Dyson coefficients at explicit μ are transported to the effective
dispersion with a scalar independent of the integration coordinates and order. -/
theorem externalInsertionVertexDysonCoefficient_eq_shiftedDispersion {E : ℕ}
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionVertexDysonCoefficient ε β μ g externalLabel externalTime n =
      externalFieldFamilyChemicalPotentialFactor μ externalLabel externalTime *
        externalInsertionVertexDysonCoefficient
          (fun k => ε k - μ) β 0 g externalLabel externalTime n := by
  unfold externalInsertionVertexDysonCoefficient
  simp only [sub_zero]
  rw [← intervalIntegral.orderedSimplexIntegral_smul]
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro σ
  rw [mul_left_comm (externalFieldFamilyChemicalPotentialFactor μ externalLabel externalTime)
    ((-1 : ℂ) ^ n)]
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [externalInsertionMixedTimeOrderedVertexComp_eq_shiftedDispersion ε μ]
  simp only [Common.finiteGibbsExpectation, map_smul, smul_eq_mul]
  ring

/-- Order-n Dyson coefficient of the explicitly mixed-time-ordered atomic
grand-canonical Gibbs operator product, including the fermionic atomic-order sign and
the vertex couplings. The Dyson (-1)^n factor is independent of the
mixed-time reordering sign. Its physical time evolution uses ε, and its
thermal occupation weight uses ε - μ. -/
noncomputable def externalInsertionMixedAtomicDysonCoefficient {E : ℕ}
    (ε : Mode → ℝ) (β μ : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ =>
      (-1 : ℂ) ^ n *
        (externalInsertionMixedAtomicOrderSign externalTime σ *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            (∏ i : Fin n, g (q i)) *
              Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - μ)) β
                (List.prod (List.ofFn
                    (fun p : Fin (2 * (2 * n + E)) =>
                      timedFieldOperator ε
                        (externalInsertionMixedTimeOrderedAtomicFieldFamily
                          externalLabel externalTime q σ p))))))

/-- At μ = 0, the mixed-atomic grand-canonical Dyson coefficient equals the existing
integrated fixed-external Wick-diagram coefficient at every perturbative
order. The finite-sum/integral interchange follows from the proved
chamberwise regularity of each diagram's Dyson integrand. -/
theorem externalInsertionMixedAtomicDysonCoefficient_eq_externalInsertionDysonCoefficient
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionMixedAtomicDysonCoefficient
        ε β 0 g externalLabel externalTime n =
      externalInsertionDysonCoefficient
        ε β g externalLabel externalTime n := by
  classical
  have hpoint (σ : Fin n → ℝ) :
      (-1 : ℂ) ^ n *
        (externalInsertionMixedAtomicOrderSign externalTime σ *
          ∑ q : Fin n → QuarticVertexLabel Mode,
            (∏ i : Fin n, g (q i)) *
              Common.finiteGibbsExpectation (fermionEnergy (fun i => ε i - (0 : ℝ))) β
                (List.prod (List.ofFn
                    (fun p : Fin (2 * (2 * n + E)) =>
                      timedFieldOperator ε
                        (externalInsertionMixedTimeOrderedAtomicFieldFamily
                          externalLabel externalTime q σ p))))) =
        ∑ d : FixedExternalInsertionWickDiagram Mode E n externalLabel,
          d.1.dysonFixedTimeAmplitude ε β g externalTime σ := by
    simp only [sub_zero]
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
