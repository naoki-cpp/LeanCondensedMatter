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

end Common
end SecondQuantization
