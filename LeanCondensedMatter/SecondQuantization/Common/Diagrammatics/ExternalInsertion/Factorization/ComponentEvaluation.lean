import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentCrossing
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

set_option linter.style.header false

/-!
# Statistics-generic component factorization of external-insertion pairing evaluation

The external-insertion component API already decomposes normalized pairs and factors the exchange
weight into an explicit inter-component factor times component-local weights. This module combines
those statistics-independent ingredients into the canonical scalar `Pairing.evaluation`
factorization.

Statistics-specific layers only need to identify the residual inter-component exchange factor with
their physical ordering sign.
-/

namespace SecondQuantization
namespace Common

open Combinatorics
open scoped BigOperators

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The scalar evaluation of an external-insertion pairing factors into the residual
inter-component exchange weight and component-local pairing evaluations whenever the pair kernel is
local under the canonical component leg embeddings. -/
theorem ExternalInsertionDiagram.evaluation_eq_inter_mul_prod_components
    (s : Statistics) {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (pairValue :
      Fin (2 * (2 * S.card + E)) → Fin (2 * (2 * S.card + E)) → ℂ)
    (localPairValue : ∀ B : d.vertexGraph.componentPartition.parts,
      Fin (2 * (2 * (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) →
      Fin (2 * (2 * (interactionSector
        (B : Finset (ExternalInsertionVertex E S))).card + d.externalPairCount B)) → ℂ)
    (hvalue : ∀ B a b,
      pairValue (d.componentDiagramLeg B a) (d.componentDiagramLeg B b) =
        localPairValue B a b) :
    d.pairing.evaluation (d.pairing.weight s) pairValue =
      (s.zetaInt : ℂ) ^ d.interComponentCrossingCount *
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.restrictComponent B).pairing.evaluation
            ((d.restrictComponent B).pairing.weight s)
            (localPairValue B) := by
  classical
  simp only [Pairing.evaluation]
  have hpair :
      (∏ pr ∈ d.pairing.pairs, pairValue pr.1 pr.2) =
        ∏ B : d.vertexGraph.componentPartition.parts,
          ∏ pr ∈ (d.restrictComponent B).pairing.pairs,
            localPairValue B pr.1 pr.2 := by
    calc
      (∏ pr ∈ d.pairing.pairs, pairValue pr.1 pr.2) =
          ∏ pr : d.pairing.NormalizedPair, pairValue pr.1.1 pr.1.2 :=
        Finset.prod_subtype _ (fun _ => Iff.rfl) _
      _ = ∏ B : d.vertexGraph.componentPartition.parts,
          ∏ pr : (d.restrictComponent B).pairing.NormalizedPair,
            pairValue
              (d.componentPairEquiv ⟨B, pr⟩).1.1
              (d.componentPairEquiv ⟨B, pr⟩).1.2 := by
        simpa using
          (Fintype.prod_equiv_sigma (d.componentPairEquiv).symm
            (fun pr => pairValue pr.1.1 pr.1.2))
      _ = ∏ B : d.vertexGraph.componentPartition.parts,
          ∏ pr : (d.restrictComponent B).pairing.NormalizedPair,
            localPairValue B pr.1.1 pr.1.2 := by
        apply Fintype.prod_congr
        intro B
        apply Fintype.prod_congr
        intro pr
        rw [d.componentPairEquiv_apply B pr]
        exact hvalue B pr.1.1 pr.1.2
      _ = ∏ B : d.vertexGraph.componentPartition.parts,
          ∏ pr ∈ (d.restrictComponent B).pairing.pairs,
            localPairValue B pr.1 pr.2 := by
        apply Fintype.prod_congr
        intro B
        exact
          (Finset.prod_subtype
            (d.restrictComponent B).pairing.pairs
            (fun _ => Iff.rfl)
            (fun pr => localPairValue B pr.1 pr.2)).symm
  rw [d.weight_eq_inter_mul_prod_components s, hpair, Finset.prod_mul_distrib]
  ring

end Common
end SecondQuantization
