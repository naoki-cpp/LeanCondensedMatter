import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockAssembly

set_option linter.style.header false

/-!
# Physical interaction-owner transport

A permutation of all ambient interaction vertices changes their physical
owners, while the external partition and its increasing source order stay
fixed. Every local interaction block is transported by an exact finite
equivalence. This is the combinatorial setup for comparing the canonical
Dyson term of an assembled diagram with its full owner-shuffle orbit.
-/

namespace SecondQuantization
namespace Common

variable {E N : ℕ}

/-- Transport the physical owner assignment along a relabeling of all
ambient interaction vertices, leaving the external source partition fixed. -/
noncomputable def ExternalInsertionBlockLayout.ownerSlotCongr
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N) : ExternalInsertionBlockLayout E N where
  partition := layout.partition
  evenBlocks := layout.evenBlocks
  interactionOwner v := layout.interactionOwner (e.symm v)

/-- The physical owner is transported by precomposition with the inverse
ambient permutation. -/
@[simp]
theorem ExternalInsertionBlockLayout.ownerSlotCongr_interactionOwner
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N) (v : Fin N) :
    (layout.ownerSlotCongr e).interactionOwner (e v) =
      layout.interactionOwner v := by
  simp [ExternalInsertionBlockLayout.ownerSlotCongr]

/-- Each actual interaction-owner fiber is transported bijectively by
the same ambient permutation; no vertex is lost or counted twice. -/
noncomputable def ExternalInsertionBlockLayout.interactionBlockOwnerSlotCongrEquiv
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N) (B : layout.partition.parts) :
    ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) B) ≃
      ↥((layout.ownerSlotCongr e).interactionBlock
        (Finset.univ : Finset (Fin N)) B) where
  toFun v := ⟨e v.1, by
    have hv : layout.interactionOwner v.1 = B :=
      (Finset.mem_filter.mp v.2).2
    simp only [ExternalInsertionBlockLayout.interactionBlock,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change layout.interactionOwner (e.symm (e v.1)) = B
    simpa using hv⟩
  invFun v := ⟨e.symm v.1, by
    have hv : (layout.ownerSlotCongr e).interactionOwner v.1 = B :=
      (Finset.mem_filter.mp v.2).2
    simp only [ExternalInsertionBlockLayout.interactionBlock,
      Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [ExternalInsertionBlockLayout.ownerSlotCongr] using hv⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

/-- The local interaction-fiber equivalence acts as the ambient
permutation on its underlying vertex label. -/
@[simp]
theorem ExternalInsertionBlockLayout.interactionBlockOwnerSlotCongrEquiv_val
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N) (B : layout.partition.parts)
    (v : ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) B)) :
    ((layout.interactionBlockOwnerSlotCongrEquiv e B v :
        ↥((layout.ownerSlotCongr e).interactionBlock
          (Finset.univ : Finset (Fin N)) B)) : Fin N) = e v.1 := rfl


/-- A physical layout whose owner of each ambient vertex is prescribed
by the block of the corresponding shuffled local slot. -/
noncomputable def ExternalInsertionBlockLayout.ofFamilyShuffle
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    {size : π.parts → ℕ}
    (σ : Combinatorics.FamilySlotShuffleTo size N) :
    ExternalInsertionBlockLayout E N where
  partition := π
  evenBlocks := heven
  interactionOwner v := (σ.slotEquiv.symm v).1

/-- Switching a fixed-size physical owner shuffle is exactly
transporting the interaction owner function by the ambient permutation.
The external source partition remains literally the same. -/
theorem ExternalInsertionBlockLayout.ofFamilyShuffle_ownerSlotCongr
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    {size : π.parts → ℕ}
    (σ τ : Combinatorics.FamilySlotShuffleTo size N) :
    (ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ).ownerSlotCongr
        (σ.ambientRelabel τ) =
      ExternalInsertionBlockLayout.ofFamilyShuffle π heven τ := by
  apply ExternalInsertionBlockLayout.ext_of_partition_owner rfl
  intro v
  apply Subtype.ext
  change
    ((σ.slotEquiv.symm ((σ.ambientRelabel τ).symm v)).1 :
      Finset (Fin (2 * E))) =
    ((τ.slotEquiv.symm v).1 : Finset (Fin (2 * E)))
  simp [Combinatorics.FamilySlotShuffleTo.ambientRelabel]



/-- View an ambient permutation on the full Fin N slot set as a
permutation of its corresponding full interaction slot subtype. -/
def fullInteractionSlotEquiv (e : Fin N ≃ Fin N) :
    ↥(Finset.univ : Finset (Fin N)) ≃
    ↥(Finset.univ : Finset (Fin N)) where
  toFun v := ⟨e v.1, Finset.mem_univ _⟩
  invFun v := ⟨e.symm v.1, Finset.mem_univ _⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

@[simp]
theorem fullInteractionSlotEquiv_val (e : Fin N ≃ Fin N)
    (v : ↥(Finset.univ : Finset (Fin N))) :
    (fullInteractionSlotEquiv e v).1 = e v.1 := rfl

/-- Change the owner of every physical interaction vertex while
transporting each local pairing and each local interaction label
through exactly the induced local slot equivalence. -/
noncomputable def ExternalInsertionBlockLayout.ownerSlotCongrBlockFamily
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B)) :
    ∀ B : (layout.ownerSlotCongr e).partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        ((layout.ownerSlotCongr e).interactionBlock
          (Finset.univ : Finset (Fin N)) B) :=
  fun B => (F B).slotCongr (layout.interactionBlockOwnerSlotCongrEquiv e B)


end Common
end SecondQuantization
