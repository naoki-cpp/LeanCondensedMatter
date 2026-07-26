import LeanCondensedMatter.SecondQuantization.Common.QuarticDiagramComponentRestriction

set_option linter.style.header false

/-!
# Products of vertex-local weights over quartic-diagram components

Products depending only on vertex-local data factor through the connected-component partition. This
is the statistics-independent scalar part of later Wick-diagram amplitude factorization.
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

/-- The Dyson recursion sign `(-1)^|S|` factors into the corresponding signs of all connected
component blocks. -/
theorem QuarticDiagram.dysonSign_eq_prod_componentSigns {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) :
    (-1 : ℂ) ^ S.card =
      ∏ B : d.componentPartition.parts, (-1 : ℂ) ^ (B : Finset (Fin N)).card := by
  classical
  rw [Finset.prod_coe_sort d.componentPartition.parts (fun B => (-1 : ℂ) ^ B.card)]
  have hpow : ∀ T : Finset (Finset (Fin N)),
      (∏ B ∈ T, (-1 : ℂ) ^ B.card) = (-1 : ℂ) ^ (∑ B ∈ T, B.card) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert B T hBT ih =>
      simp [hBT, ih, pow_add]
  rw [hpow, d.componentPartition.sum_card_parts]

end Common
end SecondQuantization
