import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentData
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing

set_option linter.style.header false

/-!
# Component factorization of arbitrary-external mixed pair contractions

The mixed-order component pair equivalence identifies every ambient normalized pair with exactly one
component-local normalized pair. The concrete free-Gibbs pair kernel is local under the corresponding
mixed-position embedding, so the ambient contraction product factors directly by the generic
`Pairing.prod_pairs_eq_prod_components` theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The product of concrete mixed-time free-Gibbs pair contractions factors over connected
components. -/
theorem ExternalInsertionWickDiagram.mixedPairContractionProduct_eq_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (∏ pr ∈ (d.pairingInMixedOrder externalTime σ).pairs,
      externalInsertionMixedTimeOrderedAtomicPairValue ε β
        d.externalLabel externalTime d.vertexLabelSequence σ pr.1 pr.2) =
      ∏ B : d.vertexGraph.componentPartition.parts,
        ∏ pr ∈ ((d.componentWickDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).pairs,
          externalInsertionMixedTimeOrderedAtomicPairValue ε β
            (d.componentWickDiagram B).externalLabel
            (d.componentExternalTime externalTime B)
            (d.componentWickDiagram B).vertexLabelSequence
            (d.componentInteractionTime σ B) pr.1 pr.2 := by
  apply Pairing.prod_pairs_eq_prod_components
    (d.pairingInMixedOrder externalTime σ)
    (fun B =>
      (d.componentWickDiagram B).pairingInMixedOrder
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B))
    (d.componentMixedPairEquiv externalTime σ)
    (externalInsertionMixedTimeOrderedAtomicPairValue ε β
      d.externalLabel externalTime d.vertexLabelSequence σ)
    (fun B =>
      externalInsertionMixedTimeOrderedAtomicPairValue ε β
        (d.componentWickDiagram B).externalLabel
        (d.componentExternalTime externalTime B)
        (d.componentWickDiagram B).vertexLabelSequence
        (d.componentInteractionTime σ B))
  intro B pr
  rw [d.componentMixedPairEquiv_apply externalTime σ B pr]
  exact d.externalInsertionMixedTimeOrderedAtomicPairValue_componentMixedPosition
    ε β externalTime σ B pr.1.1 pr.1.2

/-- The mixed-order crossing count is the sum of component-local mixed crossing counts and
the residual crossings between distinct components. -/
theorem ExternalInsertionWickDiagram.pairingInMixedOrder_crossingCount_eq_sum_components_add_inter
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder externalTime σ).crossingCount =
      (∑ B : d.vertexGraph.componentPartition.parts,
        ((d.componentWickDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).crossingCount) +
      (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
        (d.componentMixedPairEquiv externalTime σ) := by
  rw [(d.pairingInMixedOrder externalTime σ).
    crossingCount_eq_sum_componentCrossingCount_diag_add_inter
      (d.componentMixedPairEquiv externalTime σ)]
  apply congrArg (fun k : ℕ =>
    k + (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
      (d.componentMixedPairEquiv externalTime σ))
  apply Finset.sum_congr rfl
  intro B _
  exact Pairing.componentCrossingCount_self_eq
    (d.pairingInMixedOrder externalTime σ)
    ((d.componentWickDiagram B).pairingInMixedOrder
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B))
    (d.componentMixedPairEquiv externalTime σ) B
    (Equiv.refl _)
    (d.componentMixedPosition externalTime σ B)
    (d.componentMixedPosition_strictMono externalTime σ B)
    (fun pr => by
      simpa using d.componentMixedPairEquiv_apply externalTime σ B pr)

/-- The exchange-statistics weight of the mixed-order pairing factors into a residual
inter-component weight and the standalone mixed-order component weights. -/
theorem ExternalInsertionWickDiagram.pairingInMixedOrder_weight_eq_inter_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (s : Common.Statistics)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    (d.pairingInMixedOrder externalTime σ).weight s =
      (s.zetaInt : ℂ) ^
        (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
          (d.componentMixedPairEquiv externalTime σ) *
      ∏ B : d.vertexGraph.componentPartition.parts,
        ((d.componentWickDiagram B).pairingInMixedOrder
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).weight s := by
  simp only [Pairing.weight]
  rw [d.pairingInMixedOrder_crossingCount_eq_sum_components_add_inter externalTime σ,
    pow_add, ← Finset.prod_pow_eq_pow_sum]
  ac_rfl

/-- The concrete mixed pairing evaluation factors into the residual mixed inter-component fermionic
sign and the standalone mixed pairing values of all connected components. -/
theorem ExternalInsertionWickDiagram.mixedPairingValue_eq_inter_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    d.mixedPairingValue ε β externalTime σ =
      (Common.Statistics.fermion.zetaInt : ℂ) ^
        (d.pairingInMixedOrder externalTime σ).interComponentCrossingCount
          (d.componentMixedPairEquiv externalTime σ) *
      ∏ B : d.vertexGraph.componentPartition.parts,
        (d.componentWickDiagram B).mixedPairingValue ε β
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B) := by
  unfold ExternalInsertionWickDiagram.mixedPairingValue Pairing.evaluation
  rw [d.pairingInMixedOrder_weight_eq_inter_mul_prod_components
      Common.Statistics.fermion externalTime σ,
    d.mixedPairContractionProduct_eq_prod_components ε β externalTime σ,
    Finset.prod_mul_distrib]
  ring

end Fermionic
end SecondQuantization
