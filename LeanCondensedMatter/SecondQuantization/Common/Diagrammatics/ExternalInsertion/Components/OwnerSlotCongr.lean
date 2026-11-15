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

end Common
end SecondQuantization
