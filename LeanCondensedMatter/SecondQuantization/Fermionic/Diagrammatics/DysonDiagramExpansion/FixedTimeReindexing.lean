import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing

set_option linter.style.header false

/-!
# Fixed-time quartic diagram reindexing

The external-leg linked-cluster proof needs the same finite Wick-diagram reindex as the Dyson
expansion, but before ordered-simplex integration. At a fixed time assignment the sum over all
quartic diagrams is independent of the chosen vertex order: both sides are the same finite sum over
ordered vertex labels and pairings.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- A fixed-order contraction integrand in the canonical ordered-label/pairing evaluator form. -/
theorem contractionIntegrand_eq_pairingEvaluation
    {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (d : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ) :
    d.contractionIntegrand ε β order τ =
      flatVertexLegPairingEvaluation ε β
        (fun i => d.vertexLabel (order i)) τ (d.pairingInOrder order) := by
  simp only [QuarticWickDiagram.contractionIntegrand, flatVertexLegPairingEvaluation,
    Pairing.evaluation, flatVertexLegPairValue]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun pr _ => ?_)
  rw [orderedQuarticPairValue_eq_freeGibbsDensityOperator_expectation,
    orderedQuarticLegOperator]

/-- Coupling weight times a fixed-time contraction integrand in canonical evaluator form. -/
theorem couplingWeight_mul_contractionIntegrand_eq_pairingEvaluation
    {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) :
    d.couplingWeight g * d.contractionIntegrand ε β order τ =
      (∏ i : Fin S.card, g (d.vertexLabel (order i))) *
        flatVertexLegPairingEvaluation ε β
          (fun i => d.vertexLabel (order i)) τ (d.pairingInOrder order) := by
  rw [couplingWeight_eq_prod_vertexLabel_order,
    contractionIntegrand_eq_pairingEvaluation]

/-- At fixed times, summing all quartic Wick diagrams at one chosen vertex order gives the canonical
finite label/pairing sum. In particular the result is independent of the chosen vertex order. -/
theorem sum_couplingWeight_mul_contractionIntegrand_eq_pairingEvaluation
    {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ) :
    ∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.contractionIntegrand ε β order τ =
      ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          flatVertexLegPairingEvaluation ε β q τ pairing :=
  calc
    ∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.contractionIntegrand ε β order τ =
      ∑ d : QuarticWickDiagram Mode N S,
        (fun x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card =>
          (∏ i, g (x.1 i)) *
            flatVertexLegPairingEvaluation ε β x.1 τ x.2)
          (Common.quarticDiagramEquivOrderedData order d) :=
        Finset.sum_congr rfl fun d _ => by
          simp only [Common.quarticDiagramEquivOrderedData]
          exact couplingWeight_mul_contractionIntegrand_eq_pairingEvaluation
            ε β g d order τ
    _ = ∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card,
        (∏ i, g (x.1 i)) * flatVertexLegPairingEvaluation ε β x.1 τ x.2 :=
      Common.sum_quarticDiagram_eq_sum_orderedData order
        (fun x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) S.card =>
          (∏ i, g (x.1 i)) * flatVertexLegPairingEvaluation ε β x.1 τ x.2)
    _ = ∑ q : Fin S.card → QuarticVertexLabel Mode,
        ∑ pairing : Pairing (2 * S.card),
          (∏ i, g (q i)) * flatVertexLegPairingEvaluation ε β q τ pairing :=
      Fintype.sum_prod_type _
    _ = ∑ q : Fin S.card → QuarticVertexLabel Mode, (∏ i, g (q i)) *
        ∑ pairing : Pairing (2 * S.card),
          flatVertexLegPairingEvaluation ε β q τ pairing :=
      Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm

/-- The full finite fixed-time quartic Wick-diagram sum is unchanged when the vertex order is
replaced. -/
theorem sum_couplingWeight_mul_contractionIntegrand_order_independent
    {N : ℕ} {S : Finset (Fin N)}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (order₁ order₂ : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ) :
    (∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.contractionIntegrand ε β order₁ τ) =
      ∑ d : QuarticWickDiagram Mode N S,
        d.couplingWeight g * d.contractionIntegrand ε β order₂ τ := by
  rw [sum_couplingWeight_mul_contractionIntegrand_eq_pairingEvaluation
      ε β g order₁ τ,
    sum_couplingWeight_mul_contractionIntegrand_eq_pairingEvaluation
      ε β g order₂ τ]

end Fermionic
end SecondQuantization
