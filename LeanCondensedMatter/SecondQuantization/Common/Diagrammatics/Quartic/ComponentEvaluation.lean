import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentGlobalCrossingParity
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

set_option linter.style.header false

/-!
# Statistics-generic component factorization of quartic pairing evaluation

`Pairing.evaluation` is the unique scalar evaluator for a perfect pairing.  For an assembled quartic
diagram, Common already factors both pieces entering that evaluator: the Statistics-generic exchange
weight and an arbitrary scalar pair kernel.  This module combines those two structural results into
one semantic endpoint.

Concrete Bosonic/Fermionic consumers only need to supply their local pair-kernel compatibility.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- The scalar evaluation of an assembled ordered quartic pairing factors over connected components
whenever the pair kernel is local under the canonical component leg embeddings. -/
theorem QuarticDiagram.pairingInOrder_evaluation_eq_prod_components
    (s : Statistics) {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (pairValue : Fin (2 * (2 * S.card)) → Fin (2 * (2 * S.card)) → ℂ)
    (localPairValue : ∀ B : d.componentPartition.parts,
      Fin (2 * (2 * (B : Finset (Fin N)).card)) →
      Fin (2 * (2 * (B : Finset (Fin N)).card)) → ℂ)
    (hvalue : ∀ B a b,
      pairValue (d.componentOrderedLeg shuffle B a) (d.componentOrderedLeg shuffle B b) =
        localPairValue B a b) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).evaluation
        ((d.pairingInOrder (d.assembleVertexOrder orders shuffle)).weight s) pairValue =
      ∏ B : d.componentPartition.parts,
        ((d.restrictComponent B.2).pairingInOrder (orders B)).evaluation
          (((d.restrictComponent B.2).pairingInOrder (orders B)).weight s)
          (localPairValue B) := by
  classical
  simp only [Combinatorics.Pairing.evaluation]
  rw [d.pairingInOrder_weight_eq_prod_components s orders shuffle,
    d.prod_pairKernel_pairs_eq_prod_components orders shuffle pairValue localPairValue hvalue,
    ← Finset.prod_mul_distrib]

end Common
end SecondQuantization
