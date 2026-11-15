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
    classical
    simpa [ExternalInsertionBlockLayout.interactionBlock,
      ExternalInsertionBlockLayout.ownerSlotCongr] using v.2⟩
  invFun v := ⟨e.symm v.1, by
    classical
    simpa [ExternalInsertionBlockLayout.interactionBlock,
      ExternalInsertionBlockLayout.ownerSlotCongr] using v.2⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp


/-- Relabeling interaction vertices leaves every external source leg at
its exact original external insertion index. -/
@[simp]
theorem externalInsertionLegCongr_externalLeg
    {M : ℕ} {T : Finset (Fin N)} {U : Finset (Fin M)}
    (e : ↥T ≃ ↥U) (x : Fin (2 * E)) :
    externalInsertionLegCongr (E := E) e
      (externalInsertionExternalLeg E T x) =
      externalInsertionExternalLeg E U x := by
  apply (externalInsertionLegEquiv E U).injective
  simp [externalInsertionLegCongr, externalInsertionExternalLeg]

/-- Relabeling a quartic interaction vertex does not change the
corresponding local quartic leg number. -/
@[simp]
theorem externalInsertionLegCongr_interactionLeg
    {M : ℕ} {T : Finset (Fin N)} {U : Finset (Fin M)}
    (e : ↥T ≃ ↥U) (v : ↥T) (i : Fin 4) :
    externalInsertionLegCongr (E := E) e
      (externalInsertionInteractionLeg (E := E) v i) =
      externalInsertionInteractionLeg (E := E) (e v) i := by
  apply (externalInsertionLegEquiv E U).injective
  simp [externalInsertionLegCongr, externalInsertionInteractionLeg]

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
  apply ExternalInsertionBlockLayout.ext_of_partition_owner
    (left := (ExternalInsertionBlockLayout.ofFamilyShuffle π heven σ).ownerSlotCongr
      (σ.ambientRelabel τ))
    (right := ExternalInsertionBlockLayout.ofFamilyShuffle π heven τ)
    rfl
  intro v
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


/-- The physical block and local vertex selected by the interaction
equivalence commute with the global slot relabeling. All local labels
retain their original block index, even with empty interaction fibers. -/
theorem ExternalInsertionBlockLayout.ownerSlotCongr_interactionEquiv
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N)
    (v : ↥(Finset.univ : Finset (Fin N))) :
    ((layout.ownerSlotCongr e).interactionEquiv
        (Finset.univ : Finset (Fin N)) (fullInteractionSlotEquiv e v)) =
      (Equiv.sigmaCongrRight
        (fun B => layout.interactionBlockOwnerSlotCongrEquiv e B))
        (layout.interactionEquiv (Finset.univ : Finset (Fin N)) v) := by
  have hfst :
      (((layout.ownerSlotCongr e).interactionEquiv
        (Finset.univ : Finset (Fin N)) (fullInteractionSlotEquiv e v)).1) =
      ((layout.interactionEquiv (Finset.univ : Finset (Fin N)) v).1) := by
    change layout.interactionOwner (e.symm (e v.1)) =
      layout.interactionOwner v.1
    simp
  refine Sigma.ext hfst ?_
  exact (Subtype.heq_iff_coe_eq (fun _ => by simp [hfst])).2 rfl


/-- The independent local leg families are transported componentwise
along the actual ambient owner-fiber permutation. -/
noncomputable def ExternalInsertionBlockLayout.ownerSlotCongrLocalLegEquiv
    (layout : ExternalInsertionBlockLayout E N) (e : Fin N ≃ Fin N) :
    (Σ B : layout.partition.parts,
      Fin (2 * (2 * (layout.interactionBlock
        (Finset.univ : Finset (Fin N)) B).card +
        (B : Finset (Fin (2 * E))).card / 2))) ≃
    (Σ B : (layout.ownerSlotCongr e).partition.parts,
      Fin (2 * (2 * ((layout.ownerSlotCongr e).interactionBlock
        (Finset.univ : Finset (Fin N)) B).card +
        (B : Finset (Fin (2 * E))).card / 2))) :=
  Equiv.sigmaCongrRight
    (fun B => externalInsertionLegCongr
      (E := ((B : Finset (Fin (2 * E))).card / 2))
      (layout.interactionBlockOwnerSlotCongrEquiv e B))

/-- The entire flattened-leg decomposition commutes with moving the
actual owners: first move the ambient interaction vertices or first
assign each leg to its local block and move that block's vertices.
External insertion indices and all four local quartic legs are retained. -/
theorem ExternalInsertionBlockLayout.ownerSlotCongr_legEquiv
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N)
    (p : Fin (2 * (2 * (Finset.univ : Finset (Fin N)).card + E))) :
    (layout.ownerSlotCongr e).legEquiv (Finset.univ : Finset (Fin N))
        (externalInsertionLegCongr (E := E) (fullInteractionSlotEquiv e) p) =
      (layout.ownerSlotCongrLocalLegEquiv e)
        (layout.legEquiv (Finset.univ : Finset (Fin N)) p) := by
  classical
  obtain ⟨x, rfl⟩ :=
    (externalInsertionLegEquiv E (Finset.univ : Finset (Fin N))).symm.surjective p
  cases x with
  | inl x =>
    change
      (layout.ownerSlotCongr e).legEquiv (Finset.univ : Finset (Fin N))
          (externalInsertionLegCongr (E := E) (fullInteractionSlotEquiv e)
            (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N)) x)) =
        (layout.ownerSlotCongrLocalLegEquiv e)
          (layout.legEquiv (Finset.univ : Finset (Fin N))
            (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N)) x))
    simp only [externalInsertionLegCongr_externalLeg,
      ExternalInsertionBlockLayout.legEquiv_externalLeg]
    simp [ExternalInsertionBlockLayout.ownerSlotCongrLocalLegEquiv,
      externalInsertionLegCongr, externalInsertionExternalLeg,
      ExternalInsertionBlockLayout.ownerSlotCongr]
  | inr x =>
    obtain ⟨v, i⟩ := x
    change
      (layout.ownerSlotCongr e).legEquiv (Finset.univ : Finset (Fin N))
          (externalInsertionLegCongr (E := E) (fullInteractionSlotEquiv e)
            (externalInsertionInteractionLeg (E := E) v i)) =
        (layout.ownerSlotCongrLocalLegEquiv e)
          (layout.legEquiv (Finset.univ : Finset (Fin N))
            (externalInsertionInteractionLeg (E := E) v i))
    simp only [externalInsertionLegCongr_interactionLeg,
      ExternalInsertionBlockLayout.legEquiv_interactionLeg]
    rw [layout.ownerSlotCongr_interactionEquiv e v]
    simp [ExternalInsertionBlockLayout.ownerSlotCongrLocalLegEquiv,
      externalInsertionLegCongr, externalInsertionInteractionLeg]

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



/-- Conjugating each local perfect pairing by its own slot equivalence
commutes with assembling the complete independent block pairing. -/
private theorem sigmaPairing_transport
    {ι : Type*} {β γ : ι → Type*}
    (P : ∀ i, Combinatorics.PairingOn (β i))
    (e : ∀ i, β i ≃ γ i) :
    Combinatorics.PairingOn.sigmaCongrRight
        (fun i => (P i).transport (e i).symm) =
      (Combinatorics.PairingOn.sigmaCongrRight P).transport
        (Equiv.sigmaCongrRight e).symm := by
  apply Combinatorics.PairingOn.ext
  apply Equiv.ext
  rintro ⟨i, x⟩
  simp [Combinatorics.PairingOn.transport_partner,
    Combinatorics.PairingOn.sigmaCongrRight_partner]

/-- The complete physically assembled labelled Wick diagram commutes
with changing the actual ambient interaction owner assignment and
transporting all local pairings. This is an *equality of diagrams*, not
just equality of their connected partitions or unsigned weights. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_ownerSlotCongr
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (e : Fin N ≃ Fin N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B)) :
    (layout.ownerSlotCongr e).assembleDiagram
        (Finset.univ : Finset (Fin N))
        (layout.ownerSlotCongrBlockFamily e F) =
      (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).slotCongr
        (fullInteractionSlotEquiv e) := by
  classical
  let S : Finset (Fin N) := Finset.univ
  let g := externalInsertionLegCongr (E := E) (fullInteractionSlotEquiv e)
  let h := layout.ownerSlotCongrLocalLegEquiv e
  have hLeg :
      ((layout.ownerSlotCongr e).legEquiv S).trans h.symm =
        g.symm.trans (layout.legEquiv S) := by
    apply Equiv.ext
    intro p
    obtain ⟨q, rfl⟩ := g.surjective p
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    exact (congrArg h.symm (layout.ownerSlotCongr_legEquiv e q)).trans
      (h.symm_apply_apply _)
  apply ExternalInsertionDiagram.ext
  · rfl
  · funext v
    obtain ⟨w, rfl⟩ := (fullInteractionSlotEquiv e).surjective v
    change
      ((layout.ownerSlotCongrBlockFamily e F)
        (((layout.ownerSlotCongr e).interactionEquiv S
          (fullInteractionSlotEquiv e w)).1)).vertexLabel
          (((layout.ownerSlotCongr e).interactionEquiv S
            (fullInteractionSlotEquiv e w)).2) =
      (F ((layout.interactionEquiv S w).1)).vertexLabel
        ((layout.interactionEquiv S w).2)
    rw [layout.ownerSlotCongr_interactionEquiv e w]
    rfl
  · let Q : Combinatorics.PairingOn
        (Σ B : layout.partition.parts,
          Fin (2 * (2 * (layout.interactionBlock S B).card +
            (B : Finset (Fin (2 * E))).card / 2))) :=
      Combinatorics.PairingOn.sigmaCongrRight (fun B => (F B).pairing)
    have hLocal :
        Combinatorics.PairingOn.sigmaCongrRight
            (fun B => ((layout.ownerSlotCongrBlockFamily e F) B).pairing) =
          Q.transport h.symm := by
      change Combinatorics.PairingOn.sigmaCongrRight
          (fun B => ((F B).slotCongr
            (layout.interactionBlockOwnerSlotCongrEquiv e B)).pairing) =
        Q.transport h.symm
      exact sigmaPairing_transport (fun B => (F B).pairing)
        (fun B => externalInsertionLegCongr
          (E := (B : Finset (Fin (2 * E))).card / 2)
          (layout.interactionBlockOwnerSlotCongrEquiv e B))
    change
      (Combinatorics.PairingOn.sigmaCongrRight
        (fun B => ((layout.ownerSlotCongrBlockFamily e F) B).pairing)).transport
        ((layout.ownerSlotCongr e).legEquiv S) =
      (Q.transport (layout.legEquiv S)).transport g.symm
    rw [hLocal, Combinatorics.PairingOn.transport_trans,
      Combinatorics.PairingOn.transport_trans, hLeg]

end Common
end SecondQuantization
