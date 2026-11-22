import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockOrder

set_option linter.style.header false

/-!
# Connected external-insertion diagram assemblies and finite sums

Connected-block family equivalences, standardized local assignments, and
exact finite-domain reindexing of physical diagram weights.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {E N : ℕ}

/-- Connected independent labelled blocks over all ambient interaction
slots. Every block is required to be preconnected, so the assembled
diagram has no disconnected vacuum component. -/
abbrev ExternalInsertionBlockLayout.ConnectedBlockFamily
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) :=
  {F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) //
    ∀ B, (F B).vertexGraph.Preconnected}

/-- A preconnected family is equivalently a choice of a preconnected
diagram for each external block. The equivalence is exact: the common
ambient interaction vertex labels remain in their assigned fibers. -/
def ExternalInsertionBlockLayout.connectedBlockFamilyEquivPi
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) :
    layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel) ≃
      (∀ B : layout.partition.parts,
        {d : ExternalInsertionDiagram ExternalLabel InternalLabel
          ((B : Finset (Fin (2 * E))).card / 2) N
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) //
            d.vertexGraph.Preconnected}) where
  toFun F B := ⟨F.1 B, F.2 B⟩
  invFun F := ⟨fun B => (F B).1, fun B => (F B).2⟩
  left_inv F := by
    apply Subtype.ext
    funext B
    rfl
  right_inv F := by
    funext B
    apply Subtype.ext
    rfl

/-- Every independent preconnected physical block can be put on its
canonical consecutive local interaction slots. This equivalence
standardizes all blocks *simultaneously*, retaining the exact external
labels, vertex labels and oriented Wick pairing in each block.
It is the missing family-level transport needed when independent
owner assignments have the same local interaction cardinalities but
different ambient interaction subsets. Empty interaction fibers are
included in the equivalence. -/
noncomputable def ExternalInsertionBlockLayout.standardizedConnectedBlockFamilyEquiv
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N) :
    layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel) ≃
    (∀ B : layout.partition.parts,
      {d : ExternalInsertionDiagram ExternalLabel InternalLabel
          ((B : Finset (Fin (2 * E))).card / 2)
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card
          (Finset.univ : Finset (Fin
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)) //
          d.vertexGraph.Preconnected}) := by
  classical
  exact (layout.connectedBlockFamilyEquivPi
    (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)).trans
      (Equiv.piCongrRight (fun B =>
        ExternalInsertionDiagram.preconnectedSlotCongrEquiv
          (Combinatorics.standardSlotEquiv
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))))

/-- Evaluating a standardized connected-block family on a block
recovers the original local Wick diagram with its interaction vertices
relabeled by increasing ambient-slot enumeration. -/
@[simp]
theorem ExternalInsertionBlockLayout.standardizedConnectedBlockFamilyEquiv_apply
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel))
    (B : layout.partition.parts) :
    ((layout.standardizedConnectedBlockFamilyEquiv F) B).1 =
      (F.1 B).slotCongr (Combinatorics.standardSlotEquiv
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B)) := by
  rfl

open Classical in
/-- Summing a multiplicative weight over all independent connected-block
families gives the product of the individual block sums. This is a
finite algebraic factorization: no ordered-simplex integral or fermionic
sign is factored before summing the physical interaction-order shuffles. -/
theorem ExternalInsertionBlockLayout.sum_connectedBlockFamilies_prod
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [CommSemiring M]
    (layout : ExternalInsertionBlockLayout E N)
    (weight : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) → M) :
    (∑ F : layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel),
      ∏ B, weight B (F.1 B)) =
      ∏ B : layout.partition.parts,
        ∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel
            ((B : Finset (Fin (2 * E))).card / 2) N
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) //
              d.vertexGraph.Preconnected},
          weight B d.1 := by
  classical
  calc
    (∑ F : layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel), ∏ B, weight B (F.1 B)) =
      ∑ F : (∀ B : layout.partition.parts,
          {d : ExternalInsertionDiagram ExternalLabel InternalLabel
            ((B : Finset (Fin (2 * E))).card / 2) N
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) //
              d.vertexGraph.Preconnected}),
        ∏ B, weight B (F B).1 := by
          convert (Equiv.sum_comp
            (layout.connectedBlockFamilyEquivPi
              (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel))
            (fun F => ∏ B, weight B (F B).1)) using 1
          rfl
    _ = _ :=
      (Fintype.prod_sum (fun (B : layout.partition.parts)
        (d : {d : ExternalInsertionDiagram
          ExternalLabel InternalLabel
            ((B : Finset (Fin (2 * E))).card / 2) N
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) //
              d.vertexGraph.Preconnected}) => weight B d.1)).symm

open Classical in
/-- Independent connected diagrams can be summed separately even after
restricting each block by a local predicate. A simultaneous family
predicate is exactly the product of the blockwise indicators, so no
physical diagram or zero-interaction block is counted twice. -/
theorem ExternalInsertionBlockLayout.sum_connectedBlockFamilies_prod_if
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [CommSemiring M]
    (layout : ExternalInsertionBlockLayout E N)
    (condition : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) → Prop)
    (weight : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) → M) :
    (∑ F : layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel),
      if ∀ B, condition B (F.1 B) then
        ∏ B, weight B (F.1 B)
      else 0) =
      ∏ B : layout.partition.parts,
        ∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel
            ((B : Finset (Fin (2 * E))).card / 2) N
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) //
              d.vertexGraph.Preconnected},
          if condition B d.1 then weight B d.1 else 0 := by
  classical
  have hindicator
      (F : layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel)) :
      (if ∀ B, condition B (F.1 B) then
        ∏ B, weight B (F.1 B)
      else 0) =
        ∏ B, if condition B (F.1 B) then weight B (F.1 B) else 0 := by
    by_cases h : ∀ B, condition B (F.1 B)
    · simp [h]
    · obtain ⟨B, hB⟩ := not_forall.mp h
      simp only [h, ↓reduceIte]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ B) (by simp [hB])
  calc
    (∑ F : layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel),
      if ∀ B, condition B (F.1 B) then
        ∏ B, weight B (F.1 B)
      else 0) =
      ∑ F : layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel),
        ∏ B, if condition B (F.1 B) then weight B (F.1 B) else 0 := by
      apply Finset.sum_congr rfl
      intro F _
      exact hindicator F
    _ = _ := layout.sum_connectedBlockFamilies_prod
      (fun B d => if condition B d then weight B d else 0)

/-- Assemble a dependent family of connected external blocks into its
vacuum-free labelled physical diagram. -/
noncomputable def ExternalInsertionBlockLayout.assembleConnectedBlockFamily
    {ExternalLabel InternalLabel : Type*}
    (p : Σ layout : ExternalInsertionBlockLayout E N,
      layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel)) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} :=
  ⟨p.1.assembleDiagram (Finset.univ : Finset (Fin N)) p.2.1,
    p.1.hasNoVacuumComponent_assembleDiagram
      (Finset.univ : Finset (Fin N)) p.2.1 p.2.2⟩

/-- Connected block assembly is injective: the physical connected graph
recovers the exact external layout, and the assembly map recovers all
local pairing and label data. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlockFamily_injective
    {ExternalLabel InternalLabel : Type*} (anchor : Fin (2 * E)) :
    Function.Injective (ExternalInsertionBlockLayout.assembleConnectedBlockFamily
      (E := E) (N := N) (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel)) := by
  intro x y h
  rcases x with ⟨layoutX, ⟨FX, hX⟩⟩
  rcases y with ⟨layoutY, ⟨FY, hY⟩⟩
  have hdiagram :
      layoutX.assembleDiagram (Finset.univ : Finset (Fin N)) FX =
        layoutY.assembleDiagram (Finset.univ : Finset (Fin N)) FY :=
    congrArg Subtype.val h
  have hphysical :
      (layoutX.assembleDiagram (Finset.univ : Finset (Fin N)) FX).externalBlockLayout
          (layoutX.hasNoVacuumComponent_assembleDiagram
            (Finset.univ : Finset (Fin N)) FX hX) anchor =
        (layoutY.assembleDiagram (Finset.univ : Finset (Fin N)) FY).externalBlockLayout
          (layoutY.hasNoVacuumComponent_assembleDiagram
            (Finset.univ : Finset (Fin N)) FY hY) anchor :=
    ExternalInsertionDiagram.externalBlockLayout_congr hdiagram _ _ anchor
  have hlayout : layoutX = layoutY := by
    calc
      layoutX =
          (layoutX.assembleDiagram (Finset.univ : Finset (Fin N)) FX).externalBlockLayout
            (layoutX.hasNoVacuumComponent_assembleDiagram
              (Finset.univ : Finset (Fin N)) FX hX) anchor :=
        (layoutX.externalBlockLayout_assembleDiagram_eq FX hX anchor).symm
      _ = _ := hphysical
      _ = layoutY := layoutY.externalBlockLayout_assembleDiagram_eq FY hY anchor
  cases hlayout
  have hfam : FX = FY :=
    layoutX.assembleDiagram_injective (Finset.univ : Finset (Fin N)) hdiagram
  cases hfam
  rfl

/-- Any vacuum-free physical diagram is assembled from its actual external
component layout and the connected local diagrams obtained by restriction. -/
theorem ExternalInsertionBlockLayout.assembleConnectedBlockFamily_surjective
    {ExternalLabel InternalLabel : Type*} (anchor : Fin (2 * E)) :
    Function.Surjective (ExternalInsertionBlockLayout.assembleConnectedBlockFamily
      (E := E) (N := N) (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel)) := by
  intro d
  rcases d with ⟨d, hVac⟩
  let layout := d.externalBlockLayout hVac anchor
  let F := layout.restrictBlock (Finset.univ : Finset (Fin N)) d
    (d.externalBlockLayout_partner_block hVac anchor)
  refine ⟨⟨layout, ⟨F, d.restrictPhysicalBlocks_preconnected hVac anchor⟩⟩, ?_⟩
  apply Subtype.ext
  exact d.assembleDiagram_restrictPhysicalBlocks hVac anchor

/-- A vacuum-free physical diagram has a unique independent-block
description with preconnected local diagrams, including exact interaction
ownership, external labels, vertex labels and Wick pairing partners. -/
noncomputable def ExternalInsertionBlockLayout.connectedAssemblyEquiv
    {ExternalLabel InternalLabel : Type*} (anchor : Fin (2 * E)) :
    (Σ layout : ExternalInsertionBlockLayout E N,
      layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel)) ≃
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} :=
  Equiv.ofBijective
    (ExternalInsertionBlockLayout.assembleConnectedBlockFamily
      (E := E) (N := N) (ExternalLabel := ExternalLabel)
      (InternalLabel := InternalLabel))
    ⟨ExternalInsertionBlockLayout.assembleConnectedBlockFamily_injective anchor,
      ExternalInsertionBlockLayout.assembleConnectedBlockFamily_surjective anchor⟩



/-- Enumerate every independently assigned connected block family by
transporting the finite set of vacuum-free physical diagrams through the
exact assembly equivalence. This requires no arbitrary choice of a
finiteness instance for the dependent layout type. -/
noncomputable def ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
    {ExternalLabel InternalLabel : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel]
    (anchor : Fin (2 * E)) :
    Finset (Σ layout : ExternalInsertionBlockLayout E N,
      layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel)) := by
  classical
  exact (Finset.univ : Finset
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph}).image
      (ExternalInsertionBlockLayout.connectedAssemblyEquiv anchor).symm

/-- Transport a finite weighted sum across an equivalence without assuming that
the target type has a finite enumeration. -/
private theorem sum_image_equiv_symm
    {α β M : Type*} [DecidableEq β] [AddCommMonoid M]
    (e : α ≃ β) (s : Finset α) (weight : α → M) :
    (∑ b ∈ s.image e, weight (e.symm b)) = ∑ a ∈ s, weight a := by
  rw [Finset.sum_image]
  · simp only [Equiv.symm_apply_apply]
  · intro a _ b _ h
    exact e.injective h

open Classical in
/-- Every finite weighted vacuum-free diagram sum is exactly reindexed by
the full dependent family of connected local diagrams and their interaction
vertex assignments. No layout is counted twice, and the weight is evaluated
on the original assembled labelled pairing. -/
theorem ExternalInsertionBlockLayout.sum_vacuumFree_eq_sum_connectedBlockFamilies
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph}, weight d.1) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor,
        weight (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1 := by
  classical
  unfold ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
  convert (sum_image_equiv_symm
    (ExternalInsertionBlockLayout.connectedAssemblyEquiv
      (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor).symm
    Finset.univ (fun d => weight d.1)).symm using 1
  rfl


open Classical in
/-- Reindex one *fixed external-component partition fiber* of the
vacuum-free physical diagram sum by exactly those independent connected
block layouts whose prescribed source partition is the given fiber.
The equality is valid for arbitrary weights and preserves the original
labelled diagram, pairing and interaction-vertex ownership. -/
theorem ExternalInsertionBlockLayout.sum_externalPartitionFiber_eq_sum_connectedBlockFamilies
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph},
      if externalComponentPartition d.1.vertexGraph = π then weight d.1 else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.connectedAssemblyFiniteDomain
          (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor,
        if p.1.partition = π then
          weight (ExternalInsertionBlockLayout.assembleConnectedBlockFamily p).1
        else 0 := by
  classical
  rw [ExternalInsertionBlockLayout.sum_vacuumFree_eq_sum_connectedBlockFamilies
    (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
    anchor (fun d => if externalComponentPartition d.vertexGraph = π then weight d else 0)]
  apply Finset.sum_congr rfl
  intro p _
  change
    (if externalComponentPartition
        (p.1.assembleDiagram (Finset.univ : Finset (Fin N)) p.2.1).vertexGraph = π
      then weight (p.1.assembleDiagram (Finset.univ : Finset (Fin N)) p.2.1) else 0) =
      if p.1.partition = π then
        weight (p.1.assembleDiagram (Finset.univ : Finset (Fin N)) p.2.1) else 0
  rw [p.1.externalComponentPartition_assembleDiagram
    (Finset.univ : Finset (Fin N)) p.2.1 p.2.2]


/-- Restricting the physical connected-assembly domain to a prescribed
external-component partition is exactly a dependent family over the
corresponding fixed-partition layouts.  This preserves the local connected
diagram family *without* casting it to an unrelated vertex-owner fiber.
It is the dependent index bridge needed before reindexing those layouts
by their interaction orders and shuffles. -/
def ExternalInsertionBlockLayout.fixedPartitionConnectedAssemblyEquiv
    {ExternalLabel InternalLabel : Type*}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E)))) :
    {p : Σ layout : ExternalInsertionBlockLayout E N,
        layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel) //
      p.1.partition = π} ≃
      Σ layout : {layout : ExternalInsertionBlockLayout E N //
          layout.partition = π},
        layout.1.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel) where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv p := by
    rcases p with ⟨⟨layout, F⟩, hπ⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨layout, hπ⟩, F⟩
    rfl

/-- A prescribed external partition determines every physical block
layout uniquely once the owner of each ambient interaction vertex is
fixed. The external parity witnesses are propositions, not additional
diagram data. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionOwnerEquiv
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :
    {layout : ExternalInsertionBlockLayout E N // layout.partition = π} ≃
      (Fin N → π.parts) where
  toFun x := by
    rcases x with ⟨⟨partition, even, owner⟩, hp⟩
    cases hp
    exact owner
  invFun owner :=
    ⟨⟨π, heven, owner⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨partition, even, owner⟩, hp⟩ := x
    cases hp
    rfl
  right_inv owner := by
    rfl

/-- For a **fixed physical external-source partition**, layouts of all
ambient interaction vertices are in exact bijection with a variable
family of local vertex cardinalities and the shuffle interleaving those
vertices. This is the owner/shuffle reindexing required to upgrade the
genuine local Dyson shuffle-orbit factorization to a coefficientwise
partition identity.

The map is bijective even when some connected external blocks have no
interaction vertices, and counts no additional internal permutations. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :
    {layout : ExternalInsertionBlockLayout E N // layout.partition = π} ≃
      Σ size : π.parts → ℕ, FamilySlotShuffleTo size N := by
  classical
  exact (ExternalInsertionBlockLayout.fixedPartitionOwnerEquiv π heven).trans
    (ownerSizeShuffleEquiv (ι := π.parts) (total := N))

/-- A connected physical assembly of a fixed external partition is
equivalent to a unique family of local interaction sizes, one
order-preserving shuffle of those sizes, and an independent connected
diagram for every external block.

The shuffle is *the one recovered from the vertex-owner assignment*;
there are no additional independent permutations of internal vertices.
The local diagrams remain indexed by their actual interaction fibers,
including zero-size fibers. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionSizeShuffleConnectedAssemblyEquiv
    {ExternalLabel InternalLabel : Type*}
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :
    {p : Σ layout : ExternalInsertionBlockLayout E N,
        layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel) //
      p.1.partition = π} ≃
      Σ data : (Σ size : π.parts → ℕ, FamilySlotShuffleTo size N),
        (((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv (E := E) (N := N) π heven).symm data).1).ConnectedBlockFamily (ExternalLabel := ExternalLabel)
            (InternalLabel := InternalLabel) := by
  classical
  let e := ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv (E := E) (N := N) π heven
  exact (ExternalInsertionBlockLayout.fixedPartitionConnectedAssemblyEquiv
    (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) π).trans
      ((Equiv.sigmaCongrLeft
        (β := fun layout : {layout : ExternalInsertionBlockLayout E N //
            layout.partition = π} =>
          layout.1.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
            (InternalLabel := InternalLabel))
        e.symm).symm)

/-- The physical vacuum-free diagrams in one actual external-component
partition fiber are equivalent to preconnected local diagrams together
with their exact interaction-vertex owner assignment. The partition
predicate is transported by the proved graph-component identity of
the assembled diagram, rather than assumed. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionPhysicalAssemblyEquiv
    {ExternalLabel InternalLabel : Type*}
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E)))) :
    {d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
          (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph} //
      externalComponentPartition d.1.vertexGraph = π} ≃
    {p : Σ layout : ExternalInsertionBlockLayout E N,
        layout.ConnectedBlockFamily (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel) //
      p.1.partition = π} := by
  classical
  let e := ExternalInsertionBlockLayout.connectedAssemblyEquiv
    (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor
  refine Equiv.subtypeEquiv e.symm ?_
  intro d
  let p := e.symm d
  have he : (e p).1 = d.1 :=
    congrArg Subtype.val (e.apply_symm_apply d)
  have hpart : externalComponentPartition (e p).1.vertexGraph = p.1.partition :=
    p.1.externalComponentPartition_assembleDiagram
      (Finset.univ : Finset (Fin N)) p.2.1 p.2.2
  have hp : externalComponentPartition d.1.vertexGraph = p.1.partition :=
    (congrArg (fun x : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) =>
        externalComponentPartition x.vertexGraph) he.symm).trans hpart
  exact ⟨fun h => hp.symm.trans h, fun h => hp.trans h⟩

/-- Every actual vacuum-free physical Wick diagram with the specified
external-component partition is uniquely represented by (i) the local
interaction cardinality of each external block, (ii) an order-preserving
shuffle of those local slots, and (iii) one preconnected local labelled
diagram for each block. This includes empty interaction fibers. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
    {ExternalLabel InternalLabel : Type*}
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :
    {d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
          (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph} //
      externalComponentPartition d.1.vertexGraph = π} ≃
      Σ data : (Σ size : π.parts → ℕ, FamilySlotShuffleTo size N),
        (((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv (E := E) (N := N) π heven).symm data).1).ConnectedBlockFamily (ExternalLabel := ExternalLabel)
            (InternalLabel := InternalLabel) :=
  (ExternalInsertionBlockLayout.fixedPartitionPhysicalAssemblyEquiv
    (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) anchor π).trans
    (ExternalInsertionBlockLayout.fixedPartitionSizeShuffleConnectedAssemblyEquiv
      (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) π heven)

/-- A physical diagram in a prescribed even external-partition fiber has
a *unique* representation by the realized interaction-size vector, its
order-preserving owner shuffle, and a family of connected local Wick
diagrams on consecutive interaction slots.

This combines the physical size/shuffle assembly equivalence with the
existing simultaneous local standardization equivalence. Unlike an
amplitude covariance assertion, this is purely combinatorial: it keeps
the relabeling of the actual paired interaction legs explicit. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleEquiv
    {ExternalLabel InternalLabel : Type*}
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :=
  (ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
    (E := E) (N := N) (ExternalLabel := ExternalLabel)
    (InternalLabel := InternalLabel) anchor π heven).trans
    (Equiv.sigmaCongrRight (fun data =>
      ExternalInsertionBlockLayout.standardizedConnectedBlockFamilyEquiv
        (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
        (((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv
          (E := E) (N := N) π heven).symm data).1)))

/-- The physically realizable, finite size/shuffle/standardized-local
diagram data. The finiteness follows from the actual fixed-partition
Wick-diagram fiber, not from an unbounded natural-size enumeration. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleFiniteDomain
    {ExternalLabel InternalLabel : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) := by
  classical
  exact (Finset.univ : Finset
    {d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} //
      externalComponentPartition d.1.vertexGraph = π}).image
        (ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleEquiv
          (E := E) (N := N) (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel) anchor π heven)

open Classical in
/-- An arbitrary weight on physical partition-fiber diagrams can be
reindexed without loss or multiplicity by the exact finite
size/shuffle/standardized-local domain. No factorization of an
individual ordered Dyson integral is claimed. -/
theorem ExternalInsertionBlockLayout.sum_fixedPartitionPhysical_eq_standardized_sizes_shuffles
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (weight :
      {d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} //
        externalComponentPartition d.1.vertexGraph = π} → M) :
    (∑ d, weight d) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleFiniteDomain
          (E := E) (N := N) (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel) anchor π heven,
        weight ((ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleEquiv
          (E := E) (N := N) (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel) anchor π heven).symm p) := by
  classical
  simpa only [ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleFiniteDomain]
    using (sum_image_equiv_symm
      (ExternalInsertionBlockLayout.fixedPartitionPhysicalStandardizedSizeShuffleEquiv
        (E := E) (N := N) (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel) anchor π heven)
      Finset.univ weight).symm

open Classical in
/-- The finite image of the actual physical fixed-partition diagram
fiber under the exact connected-block size/shuffle equivalence. This
explicit domain avoids postulating a finiteness instance for an
unrestricted family of natural-number interaction orders. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
    {ExternalLabel InternalLabel : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :
    Finset (Σ data : (Σ size : π.parts → ℕ, FamilySlotShuffleTo size N),
      (((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv (E := E) (N := N) π heven).symm data).1).ConnectedBlockFamily (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel)) := by
  classical
  exact (Finset.univ : Finset
    {d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} //
      externalComponentPartition d.1.vertexGraph = π}).image
      (ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv (E := E) (N := N) anchor π heven)

open Classical in
/-- The *actual finite physical diagram fiber* of one even external
partition is reindexed by independently preconnected local Wick
diagrams, their exact interaction-size vector, and the unique
order-preserving owner shuffle. This works for any diagram weight,
including the fully integrated signed Dyson amplitude, and never
pretends that an individual time-ordered integral factors. -/
theorem ExternalInsertionBlockLayout.sum_fixedPartitionPhysical_eq_sizes_shuffles
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) → M) :
    (∑ d : {d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
        HasNoVacuumComponent d.vertexGraph} //
        externalComponentPartition d.1.vertexGraph = π},
      weight d.1.1) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
          anchor π heven,
        weight (((ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
          (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
          anchor π heven).symm p).1.1) := by
  classical
  simpa only [ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain]
    using (sum_image_equiv_symm
      (ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
        (E := E) (N := N) (ExternalLabel := ExternalLabel)
        (InternalLabel := InternalLabel) anchor π heven)
      Finset.univ (fun d => weight d.1.1)).symm

open Classical in
/-- Reindex a physical vacuum-free Wick diagram sum in a fixed even
external-component partition directly by interaction size vectors,
order-preserving owner shuffles and independent connected block families.
The external-partition test is an actual physical graph condition; the
weight remains attached to the original labelled Wick diagram. -/
theorem ExternalInsertionBlockLayout.sum_vacuumFree_fixedPartition_eq_sizes_shuffles
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph},
      if externalComponentPartition d.1.vertexGraph = π then weight d.1 else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
          anchor π heven,
        weight (((ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
          (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
          anchor π heven).symm p).1.1) := by
  classical
  let X := {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
    (Finset.univ : Finset (Fin N)) // HasNoVacuumComponent d.vertexGraph}
  let P : X → Prop := fun d => externalComponentPartition d.1.vertexGraph = π
  simpa only [Finset.sum_filter] using
    ((Finset.sum_subtype
      (p := P) ((Finset.univ : Finset X).filter P)
      (fun _ => by simp) (fun d : X => weight d.1)).trans
      (ExternalInsertionBlockLayout.sum_fixedPartitionPhysical_eq_sizes_shuffles
        anchor π heven weight))

/-- Evaluating the inverse physical fixed-partition size/shuffle
bijection reconstructs the actual assembled labelled Wick pairing,
including vertex labels and all external insertion legs. -/
theorem ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv_symm_diagram
    {ExternalLabel InternalLabel : Type*}
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (p : Σ data : (Σ size : π.parts → ℕ, FamilySlotShuffleTo size N),
      (((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv (E := E) (N := N) π heven).symm data).1).ConnectedBlockFamily (ExternalLabel := ExternalLabel)
          (InternalLabel := InternalLabel)) :
    (((ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv
      (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
      anchor π heven).symm p).1.1) =
      ExternalInsertionBlockLayout.assembleDiagram
        ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv (E := E) (N := N) π heven).symm p.1).1
        (Finset.univ : Finset (Fin N)) p.2.1 := by
  rfl

open Classical in
/-- The complete weighted physical fixed-partition diagram sum, now
expressed entirely in terms of the actual assembly of independent
connected local diagrams with their uniquely induced interaction
size/shuffle data. Every signed Dyson amplitude stays on the original
assembled diagram until its full shuffle orbit has been summed. -/
theorem ExternalInsertionBlockLayout.sum_vacuumFree_fixedPartition_eq_sizes_shuffles_assembled
    {ExternalLabel InternalLabel M : Type*}
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    (anchor : Fin (2 * E))
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (weight : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N)) → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N
        (Finset.univ : Finset (Fin N)) //
          HasNoVacuumComponent d.vertexGraph},
      if externalComponentPartition d.1.vertexGraph = π then weight d.1 else 0) =
      ∑ p ∈ ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleFiniteDomain
          (E := E) (N := N) (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel)
          anchor π heven,
        weight (ExternalInsertionBlockLayout.assembleDiagram
          ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv (E := E) (N := N) π heven).symm p.1).1
          (Finset.univ : Finset (Fin N)) p.2.1) := by
  classical
  rw [ExternalInsertionBlockLayout.sum_vacuumFree_fixedPartition_eq_sizes_shuffles
    anchor π heven weight]
  apply Finset.sum_congr rfl
  intro p _
  rw [ExternalInsertionBlockLayout.fixedPartitionPhysicalSizeShuffleEquiv_symm_diagram
    anchor π heven p]

/-- The exact finite collection of physical layouts with a prescribed
external partition, obtained from all actual interaction-owner functions.
No artificial finiteness instance for arbitrary size vectors is used. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionLayoutFiniteDomain
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :
    Finset {layout : ExternalInsertionBlockLayout E N // layout.partition = π} := by
  classical
  exact (Finset.univ : Finset (Fin N → π.parts)).image
    (ExternalInsertionBlockLayout.fixedPartitionOwnerEquiv π heven).symm

/-- The finite domain of actual size vectors and order-preserving
shuffles, as the exact image of the physical layout domain. Every
element of this domain is physically realizable by some vertex-owner
assignment, including all zero-vertex external components. -/
noncomputable def ExternalInsertionBlockLayout.fixedPartitionSizeShuffleFiniteDomain
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card) :
    Finset (Σ size : π.parts → ℕ, FamilySlotShuffleTo size N) := by
  classical
  exact (ExternalInsertionBlockLayout.fixedPartitionLayoutFiniteDomain π heven).image
    (ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv π heven)

/-- Reindex the **actual finite** physical layout sum at a fixed even
external-source partition by the realized local interaction sizes and
their unique owner shuffles. No unbounded enumeration of arbitrary
natural-number size vectors is assumed and no factorial is inserted. -/
theorem ExternalInsertionBlockLayout.sum_fixedPartitionLayouts_eq_sizes_shuffles
    {M : Type*} [AddCommMonoid M]
    (π : Finpartition (Finset.univ : Finset (Fin (2 * E))))
    (heven : ∀ B : π.parts, Even (B : Finset (Fin (2 * E))).card)
    (weight : ExternalInsertionBlockLayout E N → M) :
    (∑ layout ∈ ExternalInsertionBlockLayout.fixedPartitionLayoutFiniteDomain π heven,
        weight layout.1) =
      ∑ data ∈ ExternalInsertionBlockLayout.fixedPartitionSizeShuffleFiniteDomain π heven,
        weight ((ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv π heven).symm
          data).1 := by
  classical
  simpa only [ExternalInsertionBlockLayout.fixedPartitionSizeShuffleFiniteDomain] using
    (sum_image_equiv_symm
      (ExternalInsertionBlockLayout.fixedPartitionSizeShuffleEquiv π heven)
      (ExternalInsertionBlockLayout.fixedPartitionLayoutFiniteDomain π heven)
      (fun layout => weight layout.1)).symm



end Common
end SecondQuantization
