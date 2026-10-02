import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentData

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

end Fermionic
end SecondQuantization
