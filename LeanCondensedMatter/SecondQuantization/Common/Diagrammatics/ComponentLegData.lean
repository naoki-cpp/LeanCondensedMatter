import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.InteractionSector
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod

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
      ↥(Finset.toLeft B) ⊕ (↥(interactionSector B) × Local) := by
  let eLeft :
      {e : External // (Sum.inl e : External ⊕ ↥S) ∈ B} ≃
        ↥(Finset.toLeft B) :=
    (Equiv.refl External).subtypeEquiv fun _ => Finset.mem_toLeft.symm
  let eVertex :
      {v : ↥S // (Sum.inr v : External ⊕ ↥S) ∈ B} ≃
        ↥(interactionSector B) :=
    (Equiv.subtypeEquivRight fun v : ↥S =>
      (mem_interactionSector_subtype B v).symm).trans
      (Equiv.subtypeSubtypeEquivSubtype fun hv => interactionSector_subset B hv)
  let eRight :
      {p : ↥S × Local // (Sum.inr p.1 : External ⊕ ↥S) ∈ B} ≃
        ↥(interactionSector B) × Local :=
    (Equiv.prodSubtypeFstEquivSubtypeProd).trans
      (Equiv.prodCongr eVertex (Equiv.refl Local))
  exact (Equiv.subtypeSum
    (p := fun leg : External ⊕ (↥S × Local) => componentLegVertex leg ∈ B)).trans
      (Equiv.sumCongr eLeft eRight)

/-- If a component contains no external vertex, its legs are exactly its interaction vertices paired
with their local-leg data. -/
noncomputable def vacuumComponentLegDataEquiv
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


/-- If a finite leg type splits into external data and interaction-local data, and both the total
number of legs and the number of local legs per interaction vertex are even, then the external
sector has even cardinality. -/
theorem externalCardEven_of_equiv_sum_prod
    {Leg ExternalData InteractionData LocalData : Type}
    [Fintype Leg] [Fintype ExternalData] [Finite InteractionData] [Fintype LocalData]
    (legEquiv : Leg ≃ ExternalData ⊕ (InteractionData × LocalData))
    (hLeg : Even (Fintype.card Leg))
    (hLocal : Even (Fintype.card LocalData)) :
    Even (Fintype.card ExternalData) := by
  letI := Fintype.ofFinite InteractionData
  have hcard :
      Fintype.card Leg =
        Fintype.card ExternalData + Fintype.card InteractionData * Fintype.card LocalData := by
    rw [Fintype.card_congr legEquiv, Fintype.card_sum, Fintype.card_prod]
  rcases hLeg with ⟨k, hk⟩
  rcases hLocal with ⟨l, hl⟩
  rw [hl, Nat.mul_add] at hcard
  refine ⟨k - Fintype.card InteractionData * l, ?_⟩
  omega

end Common
end SecondQuantization
