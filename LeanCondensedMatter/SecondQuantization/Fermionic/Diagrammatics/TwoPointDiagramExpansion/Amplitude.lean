import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.PairingEvaluation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Fixed-time two-point Wick-diagram amplitudes

This module packages the mixed-time pairing term from the finite-temperature
Bloch--de Dominicis theorem as an amplitude of a two-point Wick diagram with fixed
external annihilation/creation labels.

The interaction times are still parameters. Ordered-simplex integration and the
Dyson factor are deliberately left to the next layer. Pair contractions are evaluated through the
canonical free Gibbs density state; finite Gibbs coordinate formulas are used only for evaluation
bridges.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Product of the quartic coupling attached to the slot-indexed interaction labels. -/
noncomputable def orderedTwoPointVertexWeight {n : ℕ}
    (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) : ℂ :=
  ∏ v, g (q v)

/-- Canonical free Gibbs density-state contraction of two mixed-time atomic positions. -/
noncomputable def mixedTimeOrderedAtomicPairValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (a b : Fin (2 * (2 * n + 1))) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperator
      ((mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ a).comp
        (mixedTimeOrderedAtomicOperatorFamily ε i j τ τ' q σ b)))

/-- The mixed-time contraction value of one slot-indexed pairing through the shared generic pairing
evaluator and the canonical density-state pair kernel. -/
noncomputable def orderedTwoPointPairingValue {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (σ : Fin n → ℝ) (q : Fin n → QuarticVertexLabel Mode)
    (pairing : Pairing (2 * n + 1)) : ℂ :=
  Common.pairingEvaluation pairing (pairing.weight Common.Statistics.fermion)
    (mixedTimeOrderedAtomicPairValue ε β i j τ τ' σ q)

/-- The mixed event-level density-state expectation is the external-order sign times the sum of
canonical pairing evaluations.  This is the semantic pairing boundary used by downstream amplitudes;
the raw finite-product expansion remains confined to the Bloch--de Dominicis specialization. -/
theorem freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (σ : Fin n → ℝ) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (mixedTimeOrderedVertexComp ε i j τ τ' q σ)) =
      twoPointExternalOrderSign τ τ' *
        ∑ pairing : Pairing (2 * n + 1),
          orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
  rw [freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairing]
  simp only [orderedTwoPointPairingValue, mixedTimeOrderedAtomicPairValue,
    Common.pairingEvaluation]

/-- Fixed-time amplitude in the slot-label/pairing representation. -/
noncomputable def orderedTwoPointFixedTimeAmplitude {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (x : OrderedTwoPointWickDiagramData Mode n) : ℂ :=
  twoPointExternalOrderSign τ τ' * orderedTwoPointVertexWeight g x.1 *
    orderedTwoPointPairingValue ε β i j τ τ' σ x.1 x.2

/-- Fixed-time amplitude of a two-point Wick diagram with the external labels fixed to
`Tτ cᵢ(τ) cⱼ†(τ')`. The pairing is evaluated after transport back to mixed-time atomic order. -/
noncomputable def FixedExternalTwoPointWickDiagram.fixedTimeAmplitude {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ
    (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ d)

/-- Summing fixed-time amplitudes over external-label-fixed diagrams is exactly the vertex-label
and mixed-order-pairing double sum. -/
theorem sum_fixedExternalTwoPointWickDiagram_fixedTimeAmplitude_eq_pairingSum
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        d.fixedTimeAmplitude ε β g τ τ' σ =
      twoPointExternalOrderSign τ τ' *
        ∑ q : Fin n → QuarticVertexLabel Mode,
          orderedTwoPointVertexWeight g q *
            ∑ pairing : Pairing (2 * n + 1),
              orderedTwoPointPairingValue ε β i j τ τ' σ q pairing := by
  calc
    ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        d.fixedTimeAmplitude ε β g τ τ' σ =
      ∑ x : OrderedTwoPointWickDiagramData Mode n,
        orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ x :=
      sum_fixedExternalTwoPointWickDiagram_eq_sum_orderedData i j τ τ' σ
        (orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ)
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

/-- Density-state form of the fixed-time external-leg Wick expansion. -/
theorem sum_fixedExternalTwoPointWickDiagram_fixedTimeAmplitude_eq_sum_vertexLabel_densityExpectation
    {n : ℕ} (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        d.fixedTimeAmplitude ε β g τ τ' σ =
      ∑ q : Fin n → QuarticVertexLabel Mode,
        orderedTwoPointVertexWeight g q *
          (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperator
              (mixedTimeOrderedVertexComp ε i j τ τ' q σ)) := by
  rw [sum_fixedExternalTwoPointWickDiagram_fixedTimeAmplitude_eq_pairingSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [freeGibbsDensityOperator_expectation_mixedTimeOrderedVertexComp_eq_sum_pairingValue]
  ring

end Fermionic
end SecondQuantization
