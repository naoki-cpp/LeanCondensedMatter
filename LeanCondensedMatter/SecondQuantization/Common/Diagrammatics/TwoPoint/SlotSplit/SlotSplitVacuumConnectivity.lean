import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Components.ComponentPartition

set_option linter.style.header false

/-!
# Vacuum connectivity across the two-point slot split

`SlotSplitConnectivity.lean` transfers connectivity on the external side of a two-point slot split.
For the linked-cluster amplitude factorization we also need the complementary statement: the
quartic vacuum piece has exactly the same adjacency and reachability as the corresponding ambient
interaction vertices after reassembly.

This module contains only that statistics-independent graph transport.  Amplitude statements belong
in the Fermionic layer.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S T : Finset (Fin N)}

/-- Adjacency in a quartic vertex graph, unfolded. -/
theorem QuarticDiagram.vertexGraph_adj_iff
    (d : QuarticDiagram InternalLabel N S) (v w : ↥S) :
    d.vertexGraph.Adj v w ↔
      v ≠ w ∧ ∃ leg : Fin (2 * (2 * S.card)),
        vertexOfLeg leg = v ∧ vertexOfLeg (d.pairing.partner leg) = w :=
  Iff.rfl

/-- The ambient interaction vertex carrying a vertex of the vacuum piece. -/
def slotSplitVacuumVertex : ↥(S \ T) → TwoPointVertex S :=
  fun v => Sum.inr ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩

/-- The vacuum-piece vertex embedding is injective. -/
theorem slotSplitVacuumVertex_injective :
    Function.Injective (slotSplitVacuumVertex (S := S) (T := T)) := by
  intro v w hvw
  have hs :
      (⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ : ↥S) =
        ⟨w.1, (Finset.mem_sdiff.mp w.2).1⟩ := by
    exact Sum.inr.inj hvw
  apply Subtype.ext
  exact congrArg (fun z : ↥S => (z : Fin N)) hs

/-- An external-piece vertex and a vacuum-piece vertex have disjoint images. -/
theorem slotSplitVertex_ne_slotSplitVacuumVertex (h : T ⊆ S)
    (x : TwoPointVertex T) (v : ↥(S \ T)) :
    slotSplitVertex h x ≠ slotSplitVacuumVertex v := by
  cases x with
  | inl e => simp [slotSplitVertex, slotSplitVacuumVertex]
  | inr w =>
      intro heq
      have hval : (w : Fin N) = (v : Fin N) := by
        simpa only [slotSplitVertex, slotSplitVacuumVertex, Sum.inr.injEq,
          Subtype.mk.injEq] using heq
      have hvnot : (v : Fin N) ∉ T := (Finset.mem_sdiff.mp v.2).2
      exact hvnot (hval ▸ w.2)

/-- A right leg of the slot splitting carries the ambient image of the corresponding quartic
vacuum-piece vertex. -/
theorem twoPointVertexOfLeg_slotLegSplitting_inr_exact (h : T ⊆ S)
    (j : Fin (2 * (2 * (S \ T).card))) :
    twoPointVertexOfLeg (slotLegSplitting h (Sum.inr j)) =
      slotSplitVacuumVertex (vertexOfLeg j) := by
  obtain ⟨p, rfl⟩ := (quarticLegEquiv (S \ T)).symm.surjective j
  obtain ⟨v, l⟩ := p
  rw [slotLegSplitting_right_interaction]
  have hvtx :
      vertexOfLeg ((quarticLegEquiv (S \ T)).symm (v, l)) = v := by
    simp [vertexOfLeg]
  rw [hvtx]
  simpa [twoPointInteractionLeg, slotSplitVacuumVertex] using
    (twoPointVertexOfLeg_interactionLeg
      (v := ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩) l)

variable (h : T ⊆ S)
  (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
  (vac : QuarticDiagram InternalLabel N (S \ T))

/-- Reassembly preserves and reflects adjacency between vertices of the vacuum piece. -/
theorem adj_ofSlotSplit_slotSplitVacuumVertex_iff (x y : ↥(S \ T)) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
        (slotSplitVacuumVertex x) (slotSplitVacuumVertex y) ↔
      vac.vertexGraph.Adj x y := by
  rw [TwoPointDiagram.vertexGraph_adj_iff, QuarticDiagram.vertexGraph_adj_iff]
  constructor
  · rintro ⟨hne, leg, hleg, hpartner⟩
    obtain ⟨z, rfl⟩ := (slotLegSplitting h).surjective leg
    cases z with
    | inl i =>
        rw [twoPointVertexOfLeg_slotLegSplitting_inl] at hleg
        exact False.elim (slotSplitVertex_ne_slotSplitVacuumVertex h _ x hleg)
    | inr j =>
        rw [twoPointVertexOfLeg_slotLegSplitting_inr_exact] at hleg
        rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inr,
          twoPointVertexOfLeg_slotLegSplitting_inr_exact] at hpartner
        refine ⟨fun hxy => hne (congrArg slotSplitVacuumVertex hxy), j, ?_, ?_⟩
        · exact slotSplitVacuumVertex_injective hleg
        · exact slotSplitVacuumVertex_injective hpartner
  · rintro ⟨hne, leg, hleg, hpartner⟩
    refine ⟨fun hxy => hne (slotSplitVacuumVertex_injective hxy),
      slotLegSplitting h (Sum.inr leg), ?_, ?_⟩
    · rw [twoPointVertexOfLeg_slotLegSplitting_inr_exact, hleg]
    · rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inr,
        twoPointVertexOfLeg_slotLegSplitting_inr_exact, hpartner]

/-- The vacuum piece maps into a reassembled two-point diagram as a graph homomorphism. -/
noncomputable def ofSlotSplitVacuumHom :
    vac.vertexGraph →g (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph where
  toFun := slotSplitVacuumVertex
  map_rel' := fun {_ _} hab =>
    (adj_ofSlotSplit_slotSplitVacuumVertex_iff h ext vac _ _).2 hab

/-- Reachability inside the vacuum piece survives reassembly. -/
theorem reachable_ofSlotSplitVacuum_of_reachable {x y : ↥(S \ T)}
    (hreach : vac.vertexGraph.Reachable x y) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      (slotSplitVacuumVertex x) (slotSplitVacuumVertex y) := by
  exact hreach.map (ofSlotSplitVacuumHom h ext vac)

/-- Every walk of a reassembled diagram starting in the vacuum piece stays in the vacuum piece. -/
theorem exists_eq_slotSplitVacuumVertex_of_adj
    {x : ↥(S \ T)} {u : TwoPointVertex S}
    (hadj : (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
      (slotSplitVacuumVertex x) u) :
    ∃ y : ↥(S \ T), u = slotSplitVacuumVertex y := by
  obtain ⟨hne, leg, hleg, hpartner⟩ :=
    ((TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph_adj_iff
      (slotSplitVacuumVertex x) u).1 hadj
  obtain ⟨z, rfl⟩ := (slotLegSplitting h).surjective leg
  cases z with
  | inl i =>
      rw [twoPointVertexOfLeg_slotLegSplitting_inl] at hleg
      exact False.elim (slotSplitVertex_ne_slotSplitVacuumVertex h _ x hleg)
  | inr j =>
      refine ⟨vertexOfLeg (vac.pairing.partner j), ?_⟩
      rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inr,
        twoPointVertexOfLeg_slotLegSplitting_inr_exact] at hpartner
      exact hpartner.symm

/-- A walk beginning in the vacuum piece can be pulled back to a reachability proof there. -/
theorem exists_reachable_of_walk_ofSlotSplitVacuum :
    ∀ {u v : TwoPointVertex S},
      (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Walk u v →
        ∀ x : ↥(S \ T), u = slotSplitVacuumVertex x →
          ∃ y : ↥(S \ T), v = slotSplitVacuumVertex y ∧ vac.vertexGraph.Reachable x y := by
  intro u v p
  induction p with
  | nil => exact fun x hx => ⟨x, hx, SimpleGraph.Reachable.refl _⟩
  | cons hadj p ih =>
      intro x hx
      subst hx
      obtain ⟨x', hx'⟩ := exists_eq_slotSplitVacuumVertex_of_adj h ext vac hadj
      obtain ⟨y, hy, hreach⟩ := ih x' hx'
      refine ⟨y, hy, SimpleGraph.Reachable.trans ?_ hreach⟩
      exact SimpleGraph.Adj.reachable
        ((adj_ofSlotSplit_slotSplitVacuumVertex_iff h ext vac x x').1 (hx' ▸ hadj))

/-- Reachability between vacuum vertices in a reassembled two-point diagram is exactly reachability
inside the quartic vacuum piece. -/
theorem reachable_ofSlotSplitVacuum_iff (x y : ↥(S \ T)) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (slotSplitVacuumVertex x) (slotSplitVacuumVertex y) ↔
      vac.vertexGraph.Reachable x y := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨y', hy', hreach⟩ :=
      exists_reachable_of_walk_ofSlotSplitVacuum h ext vac p x rfl
    have : y = y' := slotSplitVacuumVertex_injective hy'
    exact this ▸ hreach
  · exact reachable_ofSlotSplitVacuum_of_reachable h ext vac

/-- The interaction vertices in the ambient component generated by one vacuum-piece vertex are
exactly that vertex's connected component in the quartic vacuum piece. -/
theorem interactionPart_componentBlock_slotSplitVacuumVertex (v : ↥(S \ T)) :
    TwoPointDiagram.interactionPart
        ((TwoPointDiagram.ofSlotSplit h ext vac).componentBlock
          (slotSplitVacuumVertex v)) =
      vac.componentBlock v := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hxBlock⟩ := (TwoPointDiagram.mem_interactionPart _ x).1 hx
    have hreach :
        (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
          (Sum.inr ⟨x, hxS⟩ : TwoPointVertex S) (slotSplitVacuumVertex v) :=
      ((TwoPointDiagram.ofSlotSplit h ext vac).mem_componentBlock
        (slotSplitVacuumVertex v) (Sum.inr ⟨x, hxS⟩)).1 hxBlock
    have hreach' :
        (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
          (slotSplitVacuumVertex v) (Sum.inr ⟨x, hxS⟩ : TwoPointVertex S) :=
      ((TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.reachable_comm).1 hreach
    obtain ⟨p⟩ := hreach'
    obtain ⟨y, hy, hvy⟩ :=
      exists_reachable_of_walk_ofSlotSplitVacuum h ext vac p v rfl
    have hxy : x = (y : Fin N) := by
      have hs :
          (⟨x, hxS⟩ : ↥S) =
            ⟨y.1, (Finset.mem_sdiff.mp y.2).1⟩ := by
        exact Sum.inr.inj hy
      exact congrArg (fun z : ↥S => (z : Fin N)) hs
    have hymem : (y : Fin N) ∈ vac.componentBlock v :=
      (vac.mem_componentBlock v).2
        ⟨y.2, (vac.vertexGraph.reachable_comm).1 hvy⟩
    simpa [hxy] using hymem
  · intro hx
    obtain ⟨hxST, hreach⟩ := (vac.mem_componentBlock v).1 hx
    let xv : ↥(S \ T) := ⟨x, hxST⟩
    have hamb := reachable_ofSlotSplitVacuum_of_reachable h ext vac hreach
    apply (TwoPointDiagram.mem_interactionPart _ x).2
    refine ⟨(Finset.mem_sdiff.mp hxST).1, ?_⟩
    apply ((TwoPointDiagram.ofSlotSplit h ext vac).mem_componentBlock
      (slotSplitVacuumVertex v)
      (Sum.inr ⟨x, (Finset.mem_sdiff.mp hxST).1⟩)).2
    simpa [xv, slotSplitVacuumVertex] using hamb

end Common
end SecondQuantization
