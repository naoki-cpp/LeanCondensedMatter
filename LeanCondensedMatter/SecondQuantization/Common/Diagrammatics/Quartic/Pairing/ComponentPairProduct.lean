import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentDecomposition
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentProduct

set_option linter.style.header false

/-!
# Component-local pair equivalence and pair-product reindexing

The component ordered-leg embeddings assemble to an equivalence from the sigma type of all
component-local ordered legs to the assembled global ordered-leg enumeration. The generic perfect-
pairing component decomposition then identifies the component-local normalized pairs with the global
normalized pairs. Products over global pairs can therefore be reindexed over connected components.

This layer is statistics- and state-independent.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- The normalized ordered pairs of one restricted component. -/
abbrev QuarticDiagram.LocalOrderedPair {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (B : d.componentPartition.parts) :=
  ((d.restrictComponent B.2).pairingInOrder (orders B)).NormalizedPair

/-- All component-local ordered legs, assembled by a component shuffle, are equivalent to the global
ordered-leg enumeration. -/
private noncomputable def QuarticDiagram.componentOrderedLegEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts,
      Fin (2 * (2 * (B : Finset (Fin N)).card))) ≃ Fin (2 * (2 * S.card)) :=
  (Equiv.sigmaCongrRight fun B : d.componentPartition.parts =>
      orderedQuarticLegEquiv (B : Finset (Fin N)).card).trans
    (((Equiv.sigmaProdDistrib
        (fun B : d.componentPartition.parts => Fin (B : Finset (Fin N)).card)
        (Fin 4)).symm).trans
      ((Equiv.prodCongr shuffle.slotEquiv (Equiv.refl (Fin 4))).trans
        (orderedQuarticLegEquiv S.card).symm))

@[simp]
private theorem QuarticDiagram.componentOrderedLegEquiv_apply {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.componentOrderedLegEquiv shuffle ⟨B, p⟩ = d.componentOrderedLeg shuffle B p :=
  rfl

/-- Component-local normalized pairs are equivalent to the normalized pairs of the assembled global
pairing. -/
noncomputable def QuarticDiagram.componentPairEquiv {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) :
    (Σ B : d.componentPartition.parts, d.LocalOrderedPair orders B) ≃
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).NormalizedPair :=
  (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).normalizedPairSigmaEquiv
    (fun B => (d.restrictComponent B.2).pairingInOrder (orders B))
    (d.componentOrderedLegEquiv shuffle)
    (by
      intro B p
      simpa only [QuarticDiagram.componentOrderedLegEquiv_apply] using
        d.pairingInOrder_partner_componentOrderedLeg orders shuffle B p)
    (fun B => by
      simpa only [QuarticDiagram.componentOrderedLegEquiv_apply] using
        d.componentOrderedLeg_strictMono shuffle B)

@[simp]
theorem QuarticDiagram.componentPairEquiv_apply {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (pr : d.LocalOrderedPair orders B) :
    (d.componentPairEquiv orders shuffle ⟨B, pr⟩).1 =
      (d.componentOrderedLeg shuffle B pr.1.1,
        d.componentOrderedLeg shuffle B pr.1.2) := by
  simp only [QuarticDiagram.componentPairEquiv, Pairing.normalizedPairSigmaEquiv_apply,
    QuarticDiagram.componentOrderedLegEquiv_apply]

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
