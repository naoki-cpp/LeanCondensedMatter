import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalSlotSplit
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Connected
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition
import Mathlib.Combinatorics.SimpleGraph.Sum

set_option linter.style.header false

/-!
# Connectivity across the slot split

The vertex graph of a reassembled two-point diagram is the disjoint sum of the external and
quartic vacuum vertex graphs. Mathlib graph-sum reachability transfers connectivity between these
pieces and the reconstructed diagram.

Consequently, the two-point piece is externally connected exactly when its interaction-slot set is
the interaction part of the reconstructed diagram's external component. This identifies the fiber
of diagrams with external interaction set `T` with externally connected two-point pieces on `T`
paired with arbitrary quartic pieces on `S \ T`.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S T : Finset (Fin N)}

/-- The ambient vertex carrying a vertex of the external piece. -/
def slotSplitVertex (h : T ⊆ S) : TwoPointVertex T → TwoPointVertex S
  | Sum.inl e => Sum.inl e
  | Sum.inr v => Sum.inr ⟨v.1, h v.2⟩

/-- Left legs carry the ambient vertices of the corresponding external-piece vertices. -/
theorem twoPointVertexOfLeg_slotLegSplitting_inl (h : T ⊆ S)
    (i : Fin (2 * (2 * T.card + 1))) :
    twoPointVertexOfLeg (slotLegSplitting h (Sum.inl i)) =
      slotSplitVertex h (twoPointVertexOfLeg i) := by
  obtain ⟨x, rfl⟩ := (twoPointLegEquiv T).symm.surjective i
  cases x with
  | inl e =>
      rw [slotLegSplitting_external]
      simp [twoPointVertexOfLeg, slotSplitVertex]
  | inr p =>
      obtain ⟨v, l⟩ := p
      rw [slotLegSplitting_left_interaction]
      simp [twoPointVertexOfLeg, slotSplitVertex]

variable (h : T ⊆ S) (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
  (vac : QuarticDiagram InternalLabel N (S \ T))

/-- The ambient interaction vertex carrying a vertex of the vacuum piece. -/
def slotSplitVacuumVertex : ↥(S \ T) → TwoPointVertex S :=
  fun v => Sum.inr ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩

/-- Reindex the vertices of a reassembled two-point diagram by the vertices of its
external two-point and quartic vacuum pieces. -/
noncomputable def slotSplitVertexEquiv (h : T ⊆ S) :
    (TwoPointVertex T ⊕ ↥(S \ T)) ≃ TwoPointVertex S :=
  (Equiv.sumAssoc (Fin 2) ↥T ↥(S \ T)).trans
    (Equiv.sumCongr (Equiv.refl (Fin 2)) (subsetSumSdiffEquiv h))

@[simp]
theorem slotSplitVertexEquiv_inl (h : T ⊆ S) (x : TwoPointVertex T) :
    slotSplitVertexEquiv h (Sum.inl x) = slotSplitVertex h x := by
  cases x with
  | inl e => rfl
  | inr v =>
      change (Sum.inr (subsetSumSdiffEquiv h (Sum.inl v)) : TwoPointVertex S) =
        slotSplitVertex h (Sum.inr v)
      rw [subsetSumSdiffEquiv_inl_apply]
      rfl

@[simp]
theorem slotSplitVertexEquiv_inr (h : T ⊆ S) (v : ↥(S \ T)) :
    slotSplitVertexEquiv h (Sum.inr v) = slotSplitVacuumVertex v := by
  change (Sum.inr (subsetSumSdiffEquiv h (Sum.inr v)) : TwoPointVertex S) =
    slotSplitVacuumVertex v
  rw [subsetSumSdiffEquiv_inr_apply]
  rfl

/-- The external vertex embedding inherits injectivity from the slot-split equivalence. -/
private theorem slotSplitVertex_injective (h : T ⊆ S) :
    Function.Injective (slotSplitVertex h) := by
  intro x y hxy
  exact Sum.inl.inj ((slotSplitVertexEquiv h).injective
    (by simpa only [slotSplitVertexEquiv_inl] using hxy))

/-- The vacuum vertex embedding inherits injectivity from the slot-split equivalence. -/
private theorem slotSplitVacuumVertex_injective (h : T ⊆ S) :
    Function.Injective (slotSplitVacuumVertex (S := S) (T := T)) := by
  intro x y hxy
  exact Sum.inr.inj ((slotSplitVertexEquiv h).injective
    (by simpa only [slotSplitVertexEquiv_inr] using hxy))

/-- An external-piece vertex and a vacuum-piece vertex have disjoint images. -/
private theorem slotSplitVertex_ne_slotSplitVacuumVertex (h : T ⊆ S)
    (x : TwoPointVertex T) (v : ↥(S \ T)) :
    slotSplitVertex h x ≠ slotSplitVacuumVertex v := by
  intro hEq
  have hsplit : (Sum.inl x : TwoPointVertex T ⊕ ↥(S \ T)) = Sum.inr v :=
    (slotSplitVertexEquiv h).injective
      (by simpa only [slotSplitVertexEquiv_inl, slotSplitVertexEquiv_inr] using hEq)
  cases hsplit

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

/-- **A reassembled diagram induces the adjacency of its external piece.** -/
theorem adj_ofSlotSplit_slotSplitVertex_iff (x y : TwoPointVertex T) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
        (slotSplitVertex h x) (slotSplitVertex h y) ↔
      ext.vertexGraph.Adj x y := by
  constructor
  · rintro ⟨hne, leg, hleg, hpartner⟩
    obtain ⟨z, rfl⟩ := (slotLegSplitting h).surjective leg
    cases z with
    | inl i =>
        rw [twoPointVertexOfLeg_slotLegSplitting_inl] at hleg
        rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
          twoPointVertexOfLeg_slotLegSplitting_inl] at hpartner
        refine ⟨fun hxy => hne (congrArg (slotSplitVertex h) hxy), i,
          slotSplitVertex_injective h hleg, slotSplitVertex_injective h hpartner⟩
    | inr j =>
        rw [twoPointVertexOfLeg_slotLegSplitting_inr_exact] at hleg
        exact False.elim (slotSplitVertex_ne_slotSplitVacuumVertex h x _ hleg.symm)
  · rintro ⟨hne, i, hi, hpartner⟩
    refine ⟨fun hEq => hne (slotSplitVertex_injective h hEq),
      slotLegSplitting h (Sum.inl i), ?_, ?_⟩
    · rw [twoPointVertexOfLeg_slotLegSplitting_inl, hi]
    · rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
        twoPointVertexOfLeg_slotLegSplitting_inl, hpartner]

/-- Reassembly preserves and reflects adjacency between vertices of the vacuum piece. -/
private theorem adj_ofSlotSplit_slotSplitVacuumVertex_iff (x y : ↥(S \ T)) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
        (slotSplitVacuumVertex x) (slotSplitVacuumVertex y) ↔
      vac.vertexGraph.Adj x y := by
  change
    (slotSplitVacuumVertex x ≠ slotSplitVacuumVertex y ∧
      ∃ leg : Fin (2 * (2 * S.card + 1)),
        twoPointVertexOfLeg leg = slotSplitVacuumVertex x ∧
          twoPointVertexOfLeg
            ((TwoPointDiagram.ofSlotSplit h ext vac).pairing.partner leg) =
              slotSplitVacuumVertex y) ↔
      (x ≠ y ∧ ∃ leg : Fin (2 * (2 * (S \ T).card)),
        vertexOfLeg leg = x ∧ vertexOfLeg (vac.pairing.partner leg) = y)
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
        · exact slotSplitVacuumVertex_injective h hleg
        · exact slotSplitVacuumVertex_injective h hpartner
  · rintro ⟨hne, leg, hleg, hpartner⟩
    refine ⟨fun hxy => hne (slotSplitVacuumVertex_injective h hxy),
      slotLegSplitting h (Sum.inr leg), ?_, ?_⟩
    · rw [twoPointVertexOfLeg_slotLegSplitting_inr_exact, hleg]
    · rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inr,
        twoPointVertexOfLeg_slotLegSplitting_inr_exact, hpartner]

/-- The two sectors of a slot split have no edges between them. -/
private theorem not_adj_slotSplitVertex_slotSplitVacuumVertex
    (x : TwoPointVertex T) (y : ↥(S \ T)) :
    ¬ (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
      (slotSplitVertex h x) (slotSplitVacuumVertex y) := by
  intro hadj
  obtain ⟨_, leg, hleg, hpartner⟩ := hadj
  obtain ⟨z, rfl⟩ := (slotLegSplitting h).surjective leg
  cases z with
  | inl i =>
      rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
        twoPointVertexOfLeg_slotLegSplitting_inl] at hpartner
      exact slotSplitVertex_ne_slotSplitVacuumVertex h _ y hpartner
  | inr j =>
      rw [twoPointVertexOfLeg_slotLegSplitting_inr_exact] at hleg
      exact slotSplitVertex_ne_slotSplitVacuumVertex h x _ hleg.symm

/-- Reassembling a slot split produces exactly the disjoint graph sum of its two pieces. -/
noncomputable def TwoPointDiagram.ofSlotSplitVertexGraphIso :
    (ext.vertexGraph ⊕g vac.vertexGraph) ≃g
      (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph where
  toEquiv := slotSplitVertexEquiv h
  map_rel_iff' := by
    rintro (x | x) (y | y)
    · simpa only [slotSplitVertexEquiv_inl, SimpleGraph.sum_adj_inl] using
        (adj_ofSlotSplit_slotSplitVertex_iff h ext vac x y)
    · simpa [slotSplitVertexEquiv_inl, slotSplitVertexEquiv_inr, SimpleGraph.sum] using
        (not_adj_slotSplitVertex_slotSplitVacuumVertex h ext vac x y)
    · have hnot :
          ¬ (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
            (slotSplitVacuumVertex x) (slotSplitVertex h y) := by
        intro hadj
        exact not_adj_slotSplitVertex_slotSplitVacuumVertex h ext vac y x
          ((TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.adj_symm hadj)
      simpa [slotSplitVertexEquiv_inl, slotSplitVertexEquiv_inr, SimpleGraph.sum] using hnot
    · simpa only [slotSplitVertexEquiv_inr, SimpleGraph.sum_adj_inr] using
        (adj_ofSlotSplit_slotSplitVacuumVertex_iff h ext vac x y)

/-- Reachability between vertices of the external piece is exactly the restriction of
reachability in the graph of the reconstructed slot split. -/
private theorem reachable_ofSlotSplit_iff (x y : TwoPointVertex T) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (slotSplitVertex h x) (slotSplitVertex h y) ↔
      ext.vertexGraph.Reachable x y := by
  rw [← slotSplitVertexEquiv_inl h x, ← slotSplitVertexEquiv_inl h y]
  change (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      ((TwoPointDiagram.ofSlotSplitVertexGraphIso h ext vac) (Sum.inl x))
      ((TwoPointDiagram.ofSlotSplitVertexGraphIso h ext vac) (Sum.inl y)) ↔ _
  exact (SimpleGraph.Iso.reachable_iff
    (φ := TwoPointDiagram.ofSlotSplitVertexGraphIso h ext vac)
    (u := Sum.inl x) (v := Sum.inl y)).trans
      (SimpleGraph.reachable_sum_inl_iff ext.vertexGraph vac.vertexGraph x y)

/-- **The slot set of a reassembled diagram is its external component's interaction part**, provided
the external piece really is externally connected. -/
theorem interactionSector_externalComponent_ofSlotSplit
    (hext : ext.IsExternallyConnected) :
    interactionSector
        ((TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.componentBlock (Sum.inl 0)) = T := by
  classical
  ext v
  rw [mem_interactionSector]
  constructor
  · rintro ⟨hv, hmem⟩
    by_contra hvT
    let w : ↥(S \ T) := ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvT⟩⟩
    apply SimpleGraph.not_reachable_sum_inl_inr (G := ext.vertexGraph)
      (H := vac.vertexGraph) (Sum.inl (0 : Fin 2)) w
    apply (SimpleGraph.Iso.reachable_iff
      (φ := TwoPointDiagram.ofSlotSplitVertexGraphIso h ext vac)
      (u := Sum.inl (Sum.inl (0 : Fin 2))) (v := Sum.inr w)).mp
    change (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      (slotSplitVertex h (Sum.inl 0)) (slotSplitVacuumVertex w)
    simpa [slotSplitVertex, slotSplitVacuumVertex, w] using
      (((TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.mem_componentBlock
        (Sum.inl 0) (Sum.inr ⟨v, hv⟩)).1 hmem).symm
  · intro hvT
    refine ⟨h hvT, ?_⟩
    obtain ⟨e, he⟩ := hext.1 ⟨v, hvT⟩
    have hzero : ext.vertexGraph.Reachable (Sum.inl e) (Sum.inl 0) := by
      fin_cases e
      · exact SimpleGraph.Reachable.refl _
      · exact ext.externalVerticesConnected.symm
    have hreach := (reachable_ofSlotSplit_iff h ext vac
      (Sum.inr ⟨v, hvT⟩) (Sum.inl 0)).2 (he.symm.trans hzero)
    exact ((TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.mem_componentBlock
      (Sum.inl 0) (Sum.inr ⟨v, h hvT⟩)).2 (by
        simpa [slotSplitVertex] using hreach)

/-- A diagram whose external component has interaction part `T` is split by the corresponding slot
leg splitting. -/
theorem isSplit_slotLegSplitting_of_interactionSector_eq
    {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (hd : interactionSector (d.vertexGraph.componentBlock (Sum.inl 0)) = T) :
    d.pairing.IsSplit (slotLegSplitting h) := by
  subst hd
  exact d.isSplit_externalSlotLegSplitting

/-- **The external piece of such a diagram is externally connected.** -/
theorem isExternallyConnected_slotSplitExternal
    {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (hd : interactionSector (d.vertexGraph.componentBlock (Sum.inl 0)) = T)
    (hsplit : d.pairing.IsSplit (slotLegSplitting h)) :
    (d.slotSplitExternal h hsplit).IsExternallyConnected := by
  rw [TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent]
  intro v
  refine ⟨0, ?_⟩
  apply (reachable_ofSlotSplit_iff h (d.slotSplitExternal h hsplit)
    (d.slotSplitVacuum h hsplit) (Sum.inl 0) (Sum.inr v)).1
  rw [TwoPointDiagram.ofSlotSplit_slotSplit h d hsplit]
  change d.vertexGraph.Reachable (Sum.inl 0) (Sum.inr ⟨v.1, h v.2⟩)
  have hvT : (v : Fin N) ∈
      interactionSector (d.vertexGraph.componentBlock (Sum.inl 0)) := by
    rw [hd]
    exact v.2
  exact ((d.vertexGraph.mem_componentBlock (Sum.inl 0) _).1
    ((mem_interactionSector_subtype _ _).1 hvT)).symm

/-- **The fiber decomposition of the diagram sum.**

The diagrams whose external component occupies exactly the interaction vertices `T` are the pairs
consisting of an externally connected two-point diagram on `T` and an arbitrary quartic diagram on
`S \ T`.  This is the statement that lets the linked-cluster factorization organize the sum over
diagrams as a Cauchy product. -/
noncomputable def TwoPointDiagram.externalFiberEquiv :
    {d : TwoPointDiagram ExternalLabel InternalLabel N S //
        interactionSector (d.vertexGraph.componentBlock (Sum.inl 0)) = T} ≃
      {ext : TwoPointDiagram ExternalLabel InternalLabel N T // ext.IsExternallyConnected} ×
        QuarticDiagram InternalLabel N (S \ T) where
  toFun d :=
    let hsplit := isSplit_slotLegSplitting_of_interactionSector_eq h d.2
    (⟨d.1.slotSplitExternal h hsplit,
        isExternallyConnected_slotSplitExternal h d.2 hsplit⟩,
      d.1.slotSplitVacuum h hsplit)
  invFun p :=
    ⟨TwoPointDiagram.ofSlotSplit h p.1.1 p.2,
      interactionSector_externalComponent_ofSlotSplit h p.1.1 p.2 p.1.2⟩
  left_inv d :=
    Subtype.ext (TwoPointDiagram.ofSlotSplit_slotSplit h d.1
      (isSplit_slotLegSplitting_of_interactionSector_eq h d.2))
  right_inv p := by
    obtain ⟨⟨ext, hext⟩, vac⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨Subtype.ext ?_, ?_⟩
    · exact TwoPointDiagram.slotSplitExternal_ofSlotSplit h ext vac _
    · exact TwoPointDiagram.slotSplitVacuum_ofSlotSplit h ext vac _

end Common
end SecondQuantization
