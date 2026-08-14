import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentConnected

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

/-- The generic quartic vertex weight factors over component restrictions. -/
theorem QuarticDiagram.vertexWeight_eq_prod_restrictComponent
    {M : Type*} [CommMonoid M] {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (w : Label → M) :
    d.vertexWeight w =
      ∏ B : d.componentPartition.parts, (d.restrictComponent B.2).vertexWeight w := by
  simpa only [QuarticDiagram.vertexWeight] using
    (d.prod_vertexLabel_eq_prod_restrictComponent w)

/-- The generic quartic vertex weight factors over the connected component packages. -/
theorem QuarticDiagram.vertexWeight_eq_prod_restrictComponentConnected
    {M : Type*} [CommMonoid M] {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (w : Label → M) :
    d.vertexWeight w =
      ∏ B : d.componentPartition.parts,
        ((d.restrictComponentConnected B.2).1).vertexWeight w := by
  simpa only [QuarticDiagram.restrictComponentConnected] using
    (d.vertexWeight_eq_prod_restrictComponent w)

/-- The Dyson recursion sign `(-1)^|S|` factors into the corresponding signs of all connected
component blocks. -/
theorem QuarticDiagram.dysonSign_eq_prod_componentSigns {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    (-1 : ℂ) ^ S.card =
      ∏ B : d.componentPartition.parts, (-1 : ℂ) ^ (B : Finset (Fin N)).card := by
  simpa using (Finpartition.pow_card_eq_prod_parts d.componentPartition (-1 : ℂ))

/-- The statistics-independent complex Dyson sign times vertex weight factors over connected
component restrictions. -/
theorem QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_restrictComponentConnected
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (w : Label → ℂ) :
    (-1 : ℂ) ^ S.card * d.vertexWeight w =
      ∏ B : d.componentPartition.parts,
        ((-1 : ℂ) ^ (B : Finset (Fin N)).card *
          ((d.restrictComponentConnected B.2).1).vertexWeight w) := by
  rw [d.dysonSign_eq_prod_componentSigns,
    d.vertexWeight_eq_prod_restrictComponentConnected]
  rw [Finset.prod_mul_distrib]

end Common
end SecondQuantization
