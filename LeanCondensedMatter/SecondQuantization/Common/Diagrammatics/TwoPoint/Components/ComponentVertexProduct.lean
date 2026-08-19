import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition

set_option linter.style.header false

/-!
# Vertex products over external and vacuum components of two-point diagrams

The interaction vertices of a two-point diagram are canonically equivalent to the dependent sum of
the interaction parts of all full external-plus-interaction components. Reindexing finite products
along this equivalence and then separating the unique external component from the vacuum components
gives the coupling-weight and Dyson-sign factorization needed before the contraction factors are
added.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Interaction vertices are the dependent disjoint union of the interaction parts of all full
components. -/
noncomputable def TwoPointDiagram.interactionVertexComponentEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    ↥S ≃ Σ B : d.componentPartition.parts,
      ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))) :=
  d.componentPartition.equivSigmaSubfinsets S
    (fun v => (Sum.inr v : TwoPointVertex S))
    (fun _ => Finset.mem_univ _)
    (fun B => TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))
    (fun B => TwoPointDiagram.interactionPart_subset (B : Finset (TwoPointVertex S)))
    (fun B v => TwoPointDiagram.mem_interactionPart_subtype
      (B : Finset (TwoPointVertex S)) v)

@[simp]
theorem TwoPointDiagram.interactionVertexComponentEquiv_symm_val
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (x : Σ B : d.componentPartition.parts,
      ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)))) :
    ((d.interactionVertexComponentEquiv.symm x : ↥S) : Fin N) = (x.2 : Fin N) :=
  rfl

/-- A vacuum-component restriction preserves every interaction vertex label. -/
@[simp]
theorem TwoPointDiagram.restrictVacuumComponent_vertexLabel
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B)
    (v : ↥(TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex S)))) :
    (d.restrictVacuumComponent B hVac).vertexLabel v =
      d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
        (B : Finset (TwoPointVertex S)) v.2⟩ :=
  rfl

/-- A product of interaction-vertex-local weights factors over all full components. -/
theorem TwoPointDiagram.prod_vertexLabel_eq_prod_componentInteractionParts
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (w : InternalLabel → M) :
    (∏ v : ↥S, w (d.vertexLabel v)) =
      ∏ B : d.componentPartition.parts,
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) := by
  classical
  calc
    (∏ v : ↥S, w (d.vertexLabel v)) =
        ∏ x : Σ B : d.componentPartition.parts,
          ↥(TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel (d.interactionVertexComponentEquiv.symm x)) :=
      (Equiv.prod_comp d.interactionVertexComponentEquiv.symm
        (fun v => w (d.vertexLabel v))).symm
    _ = ∏ B : d.componentPartition.parts,
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) := by
      rw [Fintype.prod_sigma]
      rfl

/-- A product of interaction-vertex-local weights splits into the common external component and all
vacuum components. -/
private theorem TwoPointDiagram.prod_vertexLabel_eq_external_mul_prod_vacuum
    {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (w : InternalLabel → M) :
    (∏ v : ↥S, w (d.vertexLabel v)) =
      (∏ v : ↥(TwoPointDiagram.interactionPart (d.externalComponent 0)),
        w (d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
          (d.externalComponent 0) v.2⟩)) *
      d.vacuumComponentParts.prod fun B =>
        ∏ v : ↥(TwoPointDiagram.interactionPart
          (B : Finset (TwoPointVertex S))),
          w (d.vertexLabel ⟨v.1, TwoPointDiagram.interactionPart_subset
            (B : Finset (TwoPointVertex S)) v.2⟩) := by
  classical
  rw [d.prod_vertexLabel_eq_prod_componentInteractionParts w,
    d.prod_componentParts_eq_external_mul_prod_vacuum]
  rfl

/-- The Dyson sign factors into the external component sign and all vacuum-component signs. -/
theorem TwoPointDiagram.dysonSign_eq_external_mul_prod_vacuum
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    (-1 : ℂ) ^ S.card =
      (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
        (d.externalComponent 0)).card *
        d.vacuumComponentParts.prod (fun B =>
          (-1 : ℂ) ^ (TwoPointDiagram.interactionPart
            (B : Finset (TwoPointVertex S))).card) := by
  simpa using d.prod_vertexLabel_eq_external_mul_prod_vacuum (fun _ => (-1 : ℂ))

end Common
end SecondQuantization
