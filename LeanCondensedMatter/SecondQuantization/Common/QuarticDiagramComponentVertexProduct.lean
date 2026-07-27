import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentRestriction

set_option linter.style.header false

/-!
# Products of vertex-local weights over quartic-diagram components

The finite-partition product identities now live in
`Combinatorics/FinpartitionProduct.lean`. This module contains only the diagram-specific
compatibility between ambient and restricted vertex labels, then specializes those general
identities to the pairing-graph component partition.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- The label of a restricted vertex agrees with the ambient label under the partition's
`equivSigmaParts` inclusion. -/
@[simp]
theorem QuarticDiagram.restrictComponent_vertexLabel_equivSigmaParts
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (B : d.componentPartition.parts) (v : ↥(B : Finset (Fin N))) :
    (d.restrictComponent B.2).vertexLabel v =
      d.vertexLabel (d.componentPartition.equivSigmaParts.symm ⟨B, v⟩) := by
  apply congrArg d.vertexLabel
  apply Subtype.ext
  rw [QuarticDiagram.subtypeMemBlockEquiv_symm_val]
  rfl

/-- A product of vertex-local weights factors as the product of the corresponding products on the
connected-component restrictions. -/
theorem QuarticDiagram.prod_vertexLabel_eq_prod_restrictComponent
    {M : Type*} [CommMonoid M] {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (w : Label → M) :
    (∏ v : ↥S, w (d.vertexLabel v)) =
      ∏ B : d.componentPartition.parts,
        ∏ v : ↥(B : Finset (Fin N)), w ((d.restrictComponent B.2).vertexLabel v) := by
  simpa only [QuarticDiagram.restrictComponent_vertexLabel_equivSigmaParts] using
    (Finpartition.prod_eq_prod_parts d.componentPartition (fun v => w (d.vertexLabel v)))

/-- The Dyson recursion sign `(-1)^|S|` factors into the corresponding signs of all connected
component blocks. -/
theorem QuarticDiagram.dysonSign_eq_prod_componentSigns {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    (-1 : ℂ) ^ S.card =
      ∏ B : d.componentPartition.parts, (-1 : ℂ) ^ (B : Finset (Fin N)).card := by
  simpa using (Finpartition.pow_card_eq_prod_parts d.componentPartition (-1 : ℂ))

end Common
end SecondQuantization
