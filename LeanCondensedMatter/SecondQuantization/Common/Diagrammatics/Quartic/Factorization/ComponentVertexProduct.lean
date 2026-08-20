import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentConnected

set_option linter.style.header false

/-!
# Products of vertex-local weights over quartic-diagram components

Finite-partition product identities live in `Combinatorics/FinpartitionProduct.lean`. This module
keeps only the diagram-specific compatibility between ambient and restricted vertex labels and the
statistics-independent scalar-prefactor factorization consumed by amplitude layers.
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

/-- The statistics-independent complex Dyson sign times vertex weight factors over connected
component restrictions. -/
theorem QuarticDiagram.dysonSign_mul_vertexWeight_eq_prod_restrictComponentConnected
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (w : Label → ℂ) :
    (-1 : ℂ) ^ S.card * d.vertexWeight w =
      ∏ B : d.componentPartition.parts,
        ((-1 : ℂ) ^ (B : Finset (Fin N)).card *
          ((d.restrictComponentConnected B.2).1).vertexWeight w) := by
  have hsign :
      (-1 : ℂ) ^ S.card =
        ∏ B : d.componentPartition.parts, (-1 : ℂ) ^ (B : Finset (Fin N)).card := by
    simpa using (Finpartition.pow_card_eq_prod_parts d.componentPartition (-1 : ℂ))
  have hweight :
      d.vertexWeight w =
        ∏ B : d.componentPartition.parts,
          ((d.restrictComponentConnected B.2).1).vertexWeight w := by
    simpa only [QuarticDiagram.vertexWeight, QuarticDiagram.restrictComponentConnected,
      QuarticDiagram.restrictComponent_vertexLabel_equivSigmaParts] using
      (Finpartition.prod_eq_prod_parts d.componentPartition (fun v => w (d.vertexLabel v)))
  rw [hsign, hweight, Finset.prod_mul_distrib]

end Common
end SecondQuantization
