import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Amplitude

set_option linter.style.header false

/-!
# Dyson diagram expansion: diagram reindexing

The reindexing layer consumes the canonical `flatVertexLegPairingEvaluation` API. Expanded
crossing-weight times pair-product expressions are intentionally kept out of this boundary.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Reindexing into a sum over `QuarticWickDiagram`s -/

/-- A diagram's fixed-order ordered-simplex contribution is the integral of its canonical pairing
evaluation after transport to the chosen vertex order. -/
theorem orderedSimplexContribution_eq_pairingEvaluation {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    d.orderedSimplexContribution ε β order =
      intervalIntegral.orderedSimplexIntegral S.card β
        (fun τ => flatVertexLegPairingEvaluation ε β
          (fun i => d.vertexLabel (order i)) τ (d.pairingInOrder order)) := by
  rw [QuarticWickDiagram.orderedSimplexContribution]
  apply intervalIntegral.orderedSimplexIntegral_congr
  intro τ
  simp only [QuarticWickDiagram.contractionIntegrand, flatVertexLegPairingEvaluation,
    Combinatorics.Pairing.evaluation, flatVertexLegPairValue]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun pr _ => ?_)
  rw [orderedQuarticPairValue_eq_freeGibbsDensityOperator_expectation,
    orderedQuarticLegOperator]

/-- A diagram's coupling weight times fixed-order contribution in canonical evaluator form. -/
theorem couplingWeight_mul_orderedSimplexContribution_eq_pairingEvaluation
    {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) :
    d.couplingWeight g * d.orderedSimplexContribution ε β order =
      (∏ i : Fin S.card, g (d.vertexLabel (order i))) *
        intervalIntegral.orderedSimplexIntegral S.card β
          (fun τ => flatVertexLegPairingEvaluation ε β
            (fun i => d.vertexLabel (order i)) τ (d.pairingInOrder order)) := by
  rw [QuarticWickDiagram.couplingWeight,
    Common.QuarticDiagram.vertexWeight_eq_prod_vertexLabel_order d g order,
    orderedSimplexContribution_eq_pairingEvaluation]

/-- Summing fixed-order diagram contributions gives the vertex-label/pairing double sum in canonical
evaluator form. -/
theorem sum_couplingWeight_mul_orderedSimplexContribution_eq_pairingEvaluation
    {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (order : Common.QuarticVertexOrder S) :
    ∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.orderedSimplexContribution ε β order =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) :=
  calc
    ∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.orderedSimplexContribution ε β order =
      ∑ d : QuarticWickDiagram Mode N S,
        (fun x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card =>
          (∏ i, g (x.1 i)) *
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => flatVertexLegPairingEvaluation ε β x.1 τ x.2))
          (Common.quarticDiagramEquivOrderedData order d) :=
        Finset.sum_congr rfl fun d _ => by
          simp only [Common.quarticDiagramEquivOrderedData]
          exact couplingWeight_mul_orderedSimplexContribution_eq_pairingEvaluation ε β g d order
    _ = ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card,
        (∏ i, g (x.1 i)) *
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => flatVertexLegPairingEvaluation ε β x.1 τ x.2) :=
        Common.sum_quarticDiagram_eq_sum_orderedData order
          (fun x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card =>
            (∏ i, g (x.1 i)) *
              intervalIntegral.orderedSimplexIntegral S.card β
                (fun τ => flatVertexLegPairingEvaluation ε β x.1 τ x.2))
    _ = ∑ q : Fin S.card → QuarticVertexLabel Mode,
        ∑ pairing : Pairing (2 * S.card),
          (∏ i, g (q i)) *
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) :=
        Fintype.sum_prod_type _
    _ = ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          intervalIntegral.orderedSimplexIntegral S.card β
            (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) :=
        Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm

/-- Canonical direction of the Dyson-to-Wick-diagram expansion. -/
theorem dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude (ε : Mode → ℝ)
    (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} (S : Finset (Fin N)) :
    dysonVertexMoment ε β (quarticInteraction g) S =
      ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d := by
  symm
  rw [dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation]
  have hstep : ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d =
      (-1 : ℂ) ^ S.card * ∑ order : Common.QuarticVertexOrder S,
        ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          ∑ pairing : Pairing (2 * S.card),
            intervalIntegral.orderedSimplexIntegral S.card β
              (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
    have hpt : ∀ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d =
        (-1 : ℂ) ^ S.card *
          ∑ order : Common.QuarticVertexOrder S,
            d.couplingWeight g * d.orderedSimplexContribution ε β order :=
      fun d => by rw [quarticWickDiagramAmplitude, mul_assoc, Finset.mul_sum]
    calc
      ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
          = ∑ d : QuarticWickDiagram Mode N S, (-1 : ℂ) ^ S.card *
              ∑ order : Common.QuarticVertexOrder S,
                d.couplingWeight g * d.orderedSimplexContribution ε β order :=
          Finset.sum_congr rfl fun d _ => hpt d
      _ = (-1 : ℂ) ^ S.card * ∑ d : QuarticWickDiagram Mode N S,
            ∑ order : Common.QuarticVertexOrder S,
              d.couplingWeight g * d.orderedSimplexContribution ε β order :=
          (Finset.mul_sum _ _ _).symm
      _ = (-1 : ℂ) ^ S.card * ∑ order : Common.QuarticVertexOrder S,
            ∑ d : QuarticWickDiagram Mode N S,
              d.couplingWeight g * d.orderedSimplexContribution ε β order := by
          rw [Finset.sum_comm]
      _ = (-1 : ℂ) ^ S.card * ∑ order : Common.QuarticVertexOrder S,
            ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
              ∑ pairing : Pairing (2 * S.card),
                intervalIntegral.orderedSimplexIntegral S.card β
                  (fun τ => flatVertexLegPairingEvaluation ε β q τ pairing) := by
          congr 1
          exact Finset.sum_congr rfl fun order _ =>
            sum_couplingWeight_mul_orderedSimplexContribution_eq_pairingEvaluation ε β g order
  rw [hstep, Finset.sum_const, Finset.card_univ, Common.card_quarticVertexOrder]
  ring

/-- **The total vacuum amplitude depends only on how many vertices there are.** Two vertex sets of
equal size, in possibly different ambient index types, carry the same total Wick-diagram amplitude.

This is what lets a component of a larger diagram be scored by the perturbation coefficient at its
own order without transporting the diagram itself: `dysonVertexMoment` is
`S.card ! * normalizedDysonPartitionCoeff ε β V S.card`, which mentions `S` only through its
cardinality. -/
theorem sum_quarticWickDiagramAmplitude_eq_of_card_eq (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) {N M : ℕ} (S : Finset (Fin N)) (T : Finset (Fin M))
    (h : S.card = T.card) :
    ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d =
      ∑ d : QuarticWickDiagram Mode M T, quarticWickDiagramAmplitude ε β g d := by
  rw [← dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude,
    ← dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude,
    dysonVertexMoment, dysonVertexMoment, h]

end Fermionic
end SecondQuantization
