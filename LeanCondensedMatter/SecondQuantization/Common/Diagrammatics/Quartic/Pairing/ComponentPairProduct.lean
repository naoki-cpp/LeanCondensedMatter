import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentProduct

set_option linter.style.header false

/-!
# Quartic component pair-product reindexing

The component-pair equivalence reindexes products over the assembled global normalized pairs as
products over component-local normalized pairs. The generic perfect-pairing product theorem performs
the actual dependent-sum reindexing; this module is only the quartic adapter for endpoint kernels.

This layer is statistics- and state-independent.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- Factor a global pair kernel over the component-local normalized pairs. -/
theorem QuarticDiagram.prod_pairKernel_pairs_eq_prod_components
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (pairValue : Fin (2 * (2 * S.card)) → Fin (2 * (2 * S.card)) → ℂ)
    (localPairValue : ∀ B : d.componentPartition.parts,
      Fin (2 * (2 * (B : Finset (Fin N)).card)) →
      Fin (2 * (2 * (B : Finset (Fin N)).card)) → ℂ)
    (hvalue : ∀ B a b,
      pairValue (d.componentOrderedLeg shuffle B a) (d.componentOrderedLeg shuffle B b) =
        localPairValue B a b) :
    (∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
      pairValue pr.1 pr.2) =
      ∏ B : d.componentPartition.parts,
        ∏ pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs,
          localPairValue B pr.1 pr.2 := by
  classical
  calc
    (∏ pr ∈ (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).pairs,
        pairValue pr.1 pr.2) =
        (∏ pr : (d.pairingInOrder
          (d.assembleVertexOrder orders shuffle)).NormalizedPair,
          pairValue pr.1.1 pr.1.2) :=
      Finset.prod_subtype _ (fun _ => Iff.rfl) _
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          pairValue
            (d.componentPairEquiv orders shuffle ⟨B, pr⟩).1.1
            (d.componentPairEquiv orders shuffle ⟨B, pr⟩).1.2 :=
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).prod_componentDecomposition
        (d.componentPairEquiv orders shuffle)
        (fun pr => pairValue pr.1.1 pr.1.2)
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr : d.LocalOrderedPair orders B,
          localPairValue B pr.1.1 pr.1.2 := by
      apply Fintype.prod_congr
      intro B
      apply Fintype.prod_congr
      intro pr
      rw [d.componentPairEquiv_apply orders shuffle B pr]
      exact hvalue B pr.1.1 pr.1.2
    _ = ∏ B : d.componentPartition.parts,
        ∏ pr ∈ ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs,
          localPairValue B pr.1 pr.2 := by
      apply Fintype.prod_congr
      intro B
      exact (Finset.prod_subtype
        ((d.restrictComponent B.2).pairingInOrder (orders B)).pairs
        (fun _ => Iff.rfl)
        (fun pr => localPairValue B pr.1 pr.2)).symm

end Common
end SecondQuantization
