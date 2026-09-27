import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.InteractionSector

set_option linter.style.header false

/-!
# Component-local leg data

For diagrams whose vertices split into external and interaction sectors, an unflattened leg is either
an external leg or a local leg attached to an interaction vertex. Restricting such legs to one
component therefore splits them canonically into the component's external sector and its interaction
sector paired with the local-leg type.

This module owns that family-independent finite-set reindexing. Diagram families remain responsible
for their flattened leg enumerations and for transporting those enumerations to this common form.
-/

namespace SecondQuantization
namespace Common

variable {External Vertex Local : Type}

/-- The vertex incident to an unflattened external-or-interaction leg. -/
def componentLegVertex {S : Finset Vertex} :
    External ⊕ (↥S × Local) → External ⊕ ↥S
  | .inl e => .inl e
  | .inr p => .inr p.1

/-- Legs incident to a finite component split into its external vertices and its interaction
vertices paired with their local-leg data. -/
noncomputable def componentLegDataEquiv
    {S : Finset Vertex} (B : Finset (External ⊕ ↥S)) :
    {leg : External ⊕ (↥S × Local) // componentLegVertex leg ∈ B} ≃
      ↥(Finset.toLeft B) ⊕ (↥(interactionSector B) × Local) where
  toFun leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        exact Sum.inl ⟨e, Finset.mem_toLeft.2 hleg⟩
    | inr p =>
        exact Sum.inr
          (⟨p.1.1, (mem_interactionSector_subtype B p.1).2 hleg⟩, p.2)
  invFun leg := by
    cases leg with
    | inl e =>
        exact ⟨Sum.inl e.1, Finset.mem_toLeft.1 e.2⟩
    | inr p =>
        let v : ↥S := ⟨p.1.1, interactionSector_subset B p.1.2⟩
        exact ⟨Sum.inr (v, p.2), (mem_interactionSector_subtype B v).1 p.1.2⟩
  left_inv leg := by
    rcases leg with ⟨leg, hleg⟩
    cases leg with
    | inl e =>
        apply Subtype.ext
        rfl
    | inr p =>
        rcases p with ⟨v, l⟩
        apply Subtype.ext
        rfl
  right_inv leg := by
    cases leg with
    | inl e =>
        apply congrArg Sum.inl
        exact Subtype.ext (by rfl)
    | inr p =>
        rcases p with ⟨v, l⟩
        apply congrArg Sum.inr
        apply Prod.ext
        · exact Subtype.ext (by rfl)
        · rfl

/-- If a component contains no external vertex, its legs are exactly its interaction vertices paired
with their local-leg data. -/
noncomputable def vacuumComponentLegDataEquiv
    [DecidableEq External] [DecidableEq Vertex]
    {S : Finset Vertex} (B : Finset (External ⊕ ↥S))
    (hVac : ComponentIsVacuum B) :
    {leg : External ⊕ (↥S × Local) // componentLegVertex leg ∈ B} ≃
      ↥(interactionSector B) × Local :=
  (componentLegDataEquiv B).trans
    { toFun := fun leg => by
        cases leg with
        | inl e =>
            exact False.elim (hVac ⟨e.1, Finset.mem_toLeft.1 e.2⟩)
        | inr p => exact p
      invFun := Sum.inr
      left_inv := fun leg => by
        cases leg with
        | inl e =>
            exact False.elim (hVac ⟨e.1, Finset.mem_toLeft.1 e.2⟩)
        | inr p => rfl
      right_inv := fun _ => rfl }

end Common
end SecondQuantization
