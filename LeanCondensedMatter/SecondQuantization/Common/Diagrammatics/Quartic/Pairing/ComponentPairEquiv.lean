import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Pairing.ComponentPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentDecomposition

set_option linter.style.header false

/-!
# Quartic component-pair equivalence

The component ordered-leg embeddings assemble to an equivalence from component-local ordered legs to
the assembled global ordered-leg enumeration. The generic perfect-pairing component decomposition
then identifies the dependent sum of component-local normalized pairs with the normalized pairs of
the assembled global pairing.

This layer is statistics- and state-independent.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

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

private theorem QuarticDiagram.componentOrderedLegEquiv_partner {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.pairingInOrder (d.assembleVertexOrder orders shuffle)).partner
        (d.componentOrderedLegEquiv shuffle ⟨B, p⟩) =
      d.componentOrderedLegEquiv shuffle
        ⟨B, ((d.restrictComponent B.2).pairingInOrder (orders B)).partner p⟩ := by
  simpa only [QuarticDiagram.componentOrderedLegEquiv_apply] using
    d.pairingInOrder_partner_componentOrderedLeg orders shuffle B p

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
    (d.componentOrderedLegEquiv_partner orders shuffle)

@[simp]
theorem QuarticDiagram.componentPairEquiv_apply {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (orders : d.ComponentVertexOrders)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (pr : d.LocalOrderedPair orders B) :
    (d.componentPairEquiv orders shuffle ⟨B, pr⟩).1 =
      (d.componentOrderedLeg shuffle B pr.1.1,
        d.componentOrderedLeg shuffle B pr.1.2) := by
  simpa only [QuarticDiagram.componentPairEquiv,
      QuarticDiagram.componentOrderedLegEquiv_apply] using
    (Pairing.normalizedPairSigmaEquiv_apply_of_strictMono
      (d.pairingInOrder (d.assembleVertexOrder orders shuffle))
      (fun C => (d.restrictComponent C.2).pairingInOrder (orders C))
      (d.componentOrderedLegEquiv shuffle)
      (d.componentOrderedLegEquiv_partner orders shuffle)
      (fun C => by
        simpa only [QuarticDiagram.componentOrderedLegEquiv_apply] using
          d.componentOrderedLeg_strictMono shuffle C)
      B pr)

end Common
end SecondQuantization
