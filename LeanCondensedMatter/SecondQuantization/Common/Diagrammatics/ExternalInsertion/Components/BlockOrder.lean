import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.BlockConnectivity

set_option linter.style.header false

/-!
# Interaction-order decompositions for external blocks

Canonical shuffles of ambient quartic-vertex orders and recovery of the
physical block assignment from fully assembled connected components.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {E N : ℕ}

/-- The active interaction sectors assigned to an external partition form
an exact disjoint decomposition of the global interaction sector. In
particular, empty local interaction blocks contribute zero to this sum. -/
theorem ExternalInsertionBlockLayout.sum_interactionBlock_card_eq
    (layout : ExternalInsertionBlockLayout E N) (S : Finset (Fin N)) :
    (∑ B : layout.partition.parts, (layout.interactionBlock S B).card) = S.card := by
  classical
  have h := Fintype.card_congr (layout.interactionEquiv S)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- Every global interaction-vertex order decomposes uniquely into one
local order for each independently assigned external block and an
order-preserving shuffle of those local slots. In particular, blocks
with no interaction vertices retain their unique empty local order. -/
noncomputable def ExternalInsertionBlockLayout.interactionOrderDecompositionEquiv
    (layout : ExternalInsertionBlockLayout E N) :
    QuarticVertexOrder (Finset.univ : Finset (Fin N)) ≃
      FamilyOrdersOf
        (fun B : layout.partition.parts =>
          ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
        (fun B => (layout.interactionBlock
          (Finset.univ : Finset (Fin N)) B).card) ×
      FamilySlotShuffleTo
        (fun B : layout.partition.parts =>
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)
        (Finset.univ : Finset (Fin N)).card := by
  classical
  exact familyOrderDecompositionEquivOfSize
    (fun B : layout.partition.parts =>
      ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (fun B => (layout.interactionBlock
      (Finset.univ : Finset (Fin N)) B).card)
    (fun B => by simp)
    (layout.interactionEquiv (Finset.univ : Finset (Fin N)))

/-- The interaction vertex at each shuffled global slot is exactly
the vertex identified by the corresponding local block order. The
ambient order is arbitrary, so this applies to the actual ordered Dyson
integrand, not just the canonical increasing vertex order. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_slotVertex
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩) =
      (layout.interactionEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (layout.interactionOrderDecompositionEquiv order).1 B j⟩ := by
  classical
  let e := layout.interactionOrderDecompositionEquiv
  let data := e order
  let family : layout.partition.parts → Type :=
    fun C => ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) C)
  let size : layout.partition.parts → ℕ :=
    fun C => (layout.interactionBlock (Finset.univ : Finset (Fin N)) C).card
  let ambient := layout.interactionEquiv (Finset.univ : Finset (Fin N))
  have hassemble :
      assembleFamilyOrderOfSize family size ambient data.1 data.2 = order :=
    e.symm_apply_apply order
  change order (data.2.slotEquiv ⟨B, j⟩) =
    ambient.symm ⟨B, data.1 B j⟩
  calc
    order (data.2.slotEquiv ⟨B, j⟩) =
      (assembleFamilyOrderOfSize family size ambient data.1 data.2)
        (data.2.slotEquiv ⟨B, j⟩) := by rw [hassemble]
    _ = ambient.symm ⟨B, data.1 B j⟩ :=
      assembleFamilyOrderOfSize_slot family size ambient data.1 data.2 B j

/-- Every shuffled slot in an arbitrary global interaction order belongs
to its specified physical external-source block; interleavings cannot
move quartic vertices across assigned blocks. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_slot_owner
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    layout.interactionOwner
      (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩)).1 = B := by
  classical
  rw [layout.interactionOrderDecomposition_slotVertex order B j]
  let v := (layout.interactionOrderDecompositionEquiv order).1 B j
  have hfst :=
    congrArg Sigma.fst
      ((layout.interactionEquiv (Finset.univ : Finset (Fin N))).apply_symm_apply
        (⟨B, v⟩ : Σ C : layout.partition.parts,
          ↥(layout.interactionBlock (Finset.univ : Finset (Fin N)) C)))
  change layout.interactionOwner
    ((layout.interactionEquiv (Finset.univ : Finset (Fin N))).symm ⟨B, v⟩).1 = B at hfst
  exact hfst

/-- For an *arbitrary* global interaction-time order, the inverse
order-preserving shuffle recovers the true physical owner of the vertex
occupying each ordered-simplex slot. This is stronger than the canonical
assignment-shuffle statement: it simultaneously handles every local
interaction order and interleaving, including empty blocks. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_owner
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (v : Fin (Finset.univ : Finset (Fin N)).card) :
    ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv.symm v).1 =
      layout.interactionOwner (order v).1 := by
  classical
  let σ := (layout.interactionOrderDecompositionEquiv order).2
  rcases hslot : σ.slotEquiv.symm v with ⟨B, j⟩
  have hback : σ.slotEquiv ⟨B, j⟩ = v := by
    calc
      σ.slotEquiv ⟨B, j⟩ =
          σ.slotEquiv (σ.slotEquiv.symm v) :=
        congrArg σ.slotEquiv hslot.symm
      _ = v := σ.slotEquiv.apply_symm_apply v
  have howner := layout.interactionOrderDecomposition_slot_owner order B j
  change layout.interactionOwner (order (σ.slotEquiv ⟨B, j⟩)).1 = B at howner
  simpa only [hback] using howner.symm

/-- An assembled Wick diagram retains the *actual quartic interaction
label* at each local vertex when the ambient order is decomposed into
block-local orders and its order-preserving shuffle. This is the
vertex-label transport needed in the ordered Dyson integrand. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_vertexLabel_at_shuffledSlot
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
      (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩)) =
        (F B).vertexLabel ((layout.interactionOrderDecompositionEquiv order).1 B j) := by
  rw [layout.interactionOrderDecomposition_slotVertex order B j]
  exact layout.assembleDiagram_vertexLabel
    (Finset.univ : Finset (Fin N)) F B
    ((layout.interactionOrderDecompositionEquiv order).1 B j)

/-- Every product of physical quartic-vertex labels factors into the
products on the independently assembled blocks, with the exact local
vertex orders induced by any global Dyson time order. No permutation
multiplicity is introduced by the shuffle. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_vertexLabel_orderProduct
    {ExternalLabel InternalLabel M : Type*} [CommMonoid M]
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (g : InternalLabel → M)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N))) :
    (∏ j : Fin (Finset.univ : Finset (Fin N)).card,
      g ((layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
        (order j))) =
      ∏ B : layout.partition.parts,
        ∏ j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card,
          g ((F B).vertexLabel ((layout.interactionOrderDecompositionEquiv order).1 B j)) := by
  classical
  let shuffle := (layout.interactionOrderDecompositionEquiv order).2
  calc
    (∏ j : Fin (Finset.univ : Finset (Fin N)).card,
      g ((layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
        (order j))) =
      ∏ z : Σ B : layout.partition.parts,
        Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card,
        g ((layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).vertexLabel
          (order (shuffle.slotEquiv z))) := by
        exact (Equiv.prod_comp shuffle.slotEquiv
          (fun j => g ((layout.assembleDiagram
            (Finset.univ : Finset (Fin N)) F).vertexLabel (order j)))).symm
    _ = ∏ B : layout.partition.parts,
        ∏ j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card,
          g ((F B).vertexLabel
            ((layout.interactionOrderDecompositionEquiv order).1 B j)) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro B _
      apply Finset.prod_congr rfl
      intro j _
      exact congrArg g
        (layout.assembleDiagram_vertexLabel_at_shuffledSlot F order B j)

/-- A time attached to the global ordered-simplex slot of a
block-local interaction vertex is exactly the time pulled back along
the ambient interaction order to that vertex. No numerical re-sorting
of external insertion times is involved. -/
theorem ExternalInsertionBlockLayout.interactionOrderDecomposition_localTime
    (layout : ExternalInsertionBlockLayout E N)
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (τ : Fin (Finset.univ : Finset (Fin N)).card → ℝ)
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card) :
    τ ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv ⟨B, j⟩) =
      τ (order.symm ((layout.interactionEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (layout.interactionOrderDecompositionEquiv order).1 B j⟩)) := by
  have h := congrArg (fun v : ↥(Finset.univ : Finset (Fin N)) =>
    τ (order.symm v)) (layout.interactionOrderDecomposition_slotVertex order B j)
  simpa only [Equiv.symm_apply_apply] using h

/-- In a physically assembled Wick diagram, the actual global partner
of any quartic leg at a shuffled interaction slot is precisely the
inverse-leg transport of its original block-local partner. In particular,
no propagator can cross between source-partition blocks after any
interaction-time interleaving. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_partner_at_shuffledInteractionLeg
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (order : QuarticVertexOrder (Finset.univ : Finset (Fin N)))
    (B : layout.partition.parts)
    (j : Fin (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)
    (i : Fin 4) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).pairing.partner
      (externalInsertionInteractionLeg (E := E)
        (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv
          ⟨B, j⟩)) i) =
      (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (F B).pairing.partner
          (externalInsertionInteractionLeg
            (E := (B : Finset (Fin (2 * E))).card / 2)
            ((layout.interactionOrderDecompositionEquiv order).1 B j) i)⟩ := by
  classical
  have hleg :
      layout.legEquiv (Finset.univ : Finset (Fin N))
        (externalInsertionInteractionLeg (E := E)
          (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv
            ⟨B, j⟩)) i) =
        ⟨B, externalInsertionInteractionLeg
          (E := (B : Finset (Fin (2 * E))).card / 2)
          ((layout.interactionOrderDecompositionEquiv order).1 B j) i⟩ := by
    rw [layout.interactionOrderDecomposition_slotVertex order B j]
    rw [layout.legEquiv_interactionLeg]
    rw [(layout.interactionEquiv (Finset.univ : Finset (Fin N))).apply_symm_apply]
  have hglobal :
      externalInsertionInteractionLeg (E := E)
          (order ((layout.interactionOrderDecompositionEquiv order).2.slotEquiv
            ⟨B, j⟩)) i =
        (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
          ⟨B, externalInsertionInteractionLeg
            (E := (B : Finset (Fin (2 * E))).card / 2)
            ((layout.interactionOrderDecompositionEquiv order).1 B j) i⟩ := by
    apply (layout.legEquiv (Finset.univ : Finset (Fin N))).injective
    simpa only [Equiv.apply_symm_apply] using hleg
  rw [hglobal]
  exact layout.assembleDiagram_partner
    (Finset.univ : Finset (Fin N)) F B _

/-- The original partner of an external source leg in an assembled
diagram is the exact transport of the corresponding local external
source leg's partner. Together with the interaction-leg theorem, this
covers both kinds of atomic legs in a connected block. -/
theorem ExternalInsertionBlockLayout.assembleDiagram_partner_at_externalLeg
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (B : layout.partition.parts)
    (i : Fin (2 * ((B : Finset (Fin (2 * E))).card / 2))) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).pairing.partner
      (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N))
        (layout.sourceEquiv.symm ⟨B, i⟩)) =
      (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, (F B).pairing.partner
          (externalInsertionExternalLeg
            ((B : Finset (Fin (2 * E))).card / 2)
            (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) i)⟩ := by
  classical
  have hleg :
      layout.legEquiv (Finset.univ : Finset (Fin N))
        (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N))
          (layout.sourceEquiv.symm ⟨B, i⟩)) =
        ⟨B, externalInsertionExternalLeg
          ((B : Finset (Fin (2 * E))).card / 2)
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) i⟩ := by
    rw [layout.legEquiv_externalLeg]
    have hsource :=
      (layout.sourceEquiv).apply_symm_apply
        (⟨B, i⟩ : Σ C : layout.partition.parts,
          Fin (2 * ((C : Finset (Fin (2 * E))).card / 2)))
    rw [hsource]
  have hglobal :
      externalInsertionExternalLeg E (Finset.univ : Finset (Fin N))
        (layout.sourceEquiv.symm ⟨B, i⟩) =
      (layout.legEquiv (Finset.univ : Finset (Fin N))).symm
        ⟨B, externalInsertionExternalLeg
          ((B : Finset (Fin (2 * E))).card / 2)
          (layout.interactionBlock (Finset.univ : Finset (Fin N)) B) i⟩ := by
    apply (layout.legEquiv (Finset.univ : Finset (Fin N))).injective
    simpa only [Equiv.apply_symm_apply] using hleg
  rw [hglobal]
  exact layout.assembleDiagram_partner
    (Finset.univ : Finset (Fin N)) F B _

/-- Extract the canonical interaction-slot shuffle of an independently
assigned external-block layout from the already proved global-order
decomposition. This retains all zero-size interaction fibers and avoids
a second dependent enumeration of owner subtypes. -/
noncomputable def ExternalInsertionBlockLayout.interactionAssignmentShuffle
    (layout : ExternalInsertionBlockLayout E N) :
    FamilySlotShuffleTo
      (fun B : layout.partition.parts =>
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B).card)
      (Finset.univ : Finset (Fin N)).card :=
  (layout.interactionOrderDecompositionEquiv
    ((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).toEquiv).2

/-- Two external block layouts are equal if their source partitions and
underlying interaction-owner blocks coincide. The evenness witnesses are
propositions, so they carry no additional data. -/
theorem ExternalInsertionBlockLayout.ext_of_partition_owner
    {left right : ExternalInsertionBlockLayout E N}
    (hpart : left.partition = right.partition)
    (howner : ∀ v : Fin N,
      (left.interactionOwner v : Finset (Fin (2 * E))) =
        (right.interactionOwner v : Finset (Fin (2 * E)))) :
    left = right := by
  cases left with
  | mk π heven owner =>
    cases right with
    | mk ρ heven' owner' =>
      dsimp at hpart
      cases hpart
      have hfunc : owner = owner' := by
        funext v
        exact Subtype.ext (howner v)
      cases hfunc
      rfl

/-- At full interaction order, reconstructing the physical connected
components of an independently assembled family of preconnected local
diagrams recovers its *entire original layout*, not just the external
partition or individual active interaction owners. -/
theorem ExternalInsertionBlockLayout.externalBlockLayout_assembleDiagram_eq
    {ExternalLabel InternalLabel : Type*}
    (layout : ExternalInsertionBlockLayout E N)
    (F : ∀ B : layout.partition.parts,
      ExternalInsertionDiagram ExternalLabel InternalLabel
        ((B : Finset (Fin (2 * E))).card / 2) N
        (layout.interactionBlock (Finset.univ : Finset (Fin N)) B))
    (hconnected : ∀ B, (F B).vertexGraph.Preconnected)
    (anchor : Fin (2 * E)) :
    (layout.assembleDiagram (Finset.univ : Finset (Fin N)) F).externalBlockLayout
        (layout.hasNoVacuumComponent_assembleDiagram
          (Finset.univ : Finset (Fin N)) F hconnected) anchor = layout := by
  apply ExternalInsertionBlockLayout.ext_of_partition_owner
  · exact layout.externalComponentPartition_assembleDiagram
      (Finset.univ : Finset (Fin N)) F hconnected
  · intro v
    exact layout.externalBlockLayout_assembleDiagram_interactionOwner
      (Finset.univ : Finset (Fin N)) F hconnected anchor
      ⟨v, Finset.mem_univ v⟩



/-- The physical block layout depends only on the labelled diagram,
not on which proof of absence of vacuum components is supplied. -/
theorem ExternalInsertionDiagram.externalBlockLayout_congr
    {ExternalLabel InternalLabel : Type*}
    {d e : ExternalInsertionDiagram ExternalLabel InternalLabel E N
      (Finset.univ : Finset (Fin N))}
    (h : d = e)
    (hVacD : HasNoVacuumComponent d.vertexGraph)
    (hVacE : HasNoVacuumComponent e.vertexGraph)
    (anchor : Fin (2 * E)) :
    d.externalBlockLayout hVacD anchor = e.externalBlockLayout hVacE anchor := by
  subst e
  rfl


end Common
end SecondQuantization
