import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentRestriction

set_option linter.style.header false

/-!
# Products of vertex-local weights over quartic-diagram components

A product depending only on each vertex label factors through the connected-component partition.
This is the statistics-independent scalar part of later Wick-diagram amplitude factorization.
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
  classical
  calc
    (∏ v : ↥S, w (d.vertexLabel v)) =
        ∏ x : Σ B : d.componentPartition.parts, ↥(B : Finset (Fin N)),
          w ((d.restrictComponent x.1.2).vertexLabel x.2) := by
      refine Fintype.prod_equiv d.componentPartition.equivSigmaParts
        (fun v => w (d.vertexLabel v))
        (fun x => w ((d.restrictComponent x.1.2).vertexLabel x.2)) ?_
      intro v
      rw [QuarticDiagram.restrictComponent_vertexLabel_equivSigmaParts]
      simp
    _ = ∏ B : d.componentPartition.parts,
        ∏ v : ↥(B : Finset (Fin N)), w ((d.restrictComponent B.2).vertexLabel v) :=
      Fintype.prod_sigma _

end Common
end SecondQuantization
