import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalSlotSplit

set_option linter.style.header false

/-!
# Connectivity across the slot split

`TwoPointDiagram.slotSplitEquiv` identifies the diagrams whose pairing does not cross a slot divide
with pairs of pieces, but says nothing about connectivity.  This module supplies the transfer that
the linked-cluster fiber decomposition needs: reachability inside a reassembled diagram, restricted
to the vertices of the external piece, is exactly reachability inside that piece.

The mechanism is that no contraction of a reassembled pairing joins the two blocks, so a walk that
starts at a vertex of the external piece can never leave it.  Consequently

* the external piece of a reassembled diagram is externally connected exactly when the slot set is
  the interaction part of the reassembled diagram's external component, and
* the diagrams whose external component has interaction part `T` are exactly the pairs consisting of
  an externally connected piece on `T` and an arbitrary vacuum piece on `S \ T`.

That last statement is the fiber decomposition itself.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S T : Finset (Fin N)}

/-- Adjacency in a two-point vertex graph, unfolded. -/
theorem TwoPointDiagram.vertexGraph_adj_iff
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (v w : TwoPointVertex S) :
    d.vertexGraph.Adj v w ↔
      v ≠ w ∧ ∃ leg : Fin (2 * (2 * S.card + 1)),
        twoPointVertexOfLeg leg = v ∧
          twoPointVertexOfLeg (d.pairing.partner leg) = w :=
  Iff.rfl

/-- The ambient vertex carrying a vertex of the external piece. -/
def slotSplitVertex (h : T ⊆ S) : TwoPointVertex T → TwoPointVertex S
  | Sum.inl e => Sum.inl e
  | Sum.inr v => Sum.inr ⟨v.1, h v.2⟩

theorem slotSplitVertex_injective (h : T ⊆ S) :
    Function.Injective (slotSplitVertex h) := by
  rintro (e | v) (f | w) hEq
  · simpa [slotSplitVertex] using hEq
  · simp [slotSplitVertex] at hEq
  · simp [slotSplitVertex] at hEq
  · simp only [slotSplitVertex, Sum.inr.injEq] at hEq
    exact congrArg Sum.inr (Subtype.ext (congrArg Subtype.val hEq))

/-- A vertex of the external piece is never an interaction vertex outside the slot set. -/
theorem slotSplitVertex_ne_inr_of_not_mem (h : T ⊆ S) (x : TwoPointVertex T) {w : ↥S}
    (hw : (w : Fin N) ∉ T) : slotSplitVertex h x ≠ Sum.inr w := by
  cases x with
  | inl e => simp [slotSplitVertex]
  | inr v =>
      simp only [slotSplitVertex, ne_eq, Sum.inr.injEq]
      intro hEq
      exact hw (by
        have : (v : Fin N) = (w : Fin N) := congrArg Subtype.val hEq
        exact this ▸ v.2)

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

/-- Right legs carry interaction vertices outside the slot set. -/
theorem exists_not_mem_twoPointVertexOfLeg_slotLegSplitting_inr (h : T ⊆ S)
    (i : Fin (2 * (2 * (S \ T).card))) :
    ∃ w : ↥S, (w : Fin N) ∉ T ∧
      twoPointVertexOfLeg (slotLegSplitting h (Sum.inr i)) = Sum.inr w := by
  obtain ⟨p, rfl⟩ := (quarticLegEquiv (S \ T)).symm.surjective i
  obtain ⟨v, l⟩ := p
  refine ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, (Finset.mem_sdiff.mp v.2).2, ?_⟩
  rw [slotLegSplitting_right_interaction]
  simp [twoPointVertexOfLeg]

variable (h : T ⊆ S) (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
  (vac : QuarticDiagram InternalLabel N (S \ T))

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
        obtain ⟨w, hw, hvert⟩ :=
          exists_not_mem_twoPointVertexOfLeg_slotLegSplitting_inr h j
        exact absurd (hvert.symm.trans hleg).symm (slotSplitVertex_ne_inr_of_not_mem h x hw)
  · rintro ⟨hne, i, hi, hpartner⟩
    refine ⟨fun hEq => hne (slotSplitVertex_injective h hEq),
      slotLegSplitting h (Sum.inl i), ?_, ?_⟩
    · rw [twoPointVertexOfLeg_slotLegSplitting_inl, hi]
    · rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
        twoPointVertexOfLeg_slotLegSplitting_inl, hpartner]

/-- **A walk cannot leave the external piece.** -/
theorem exists_eq_slotSplitVertex_of_adj {x : TwoPointVertex T} {u : TwoPointVertex S}
    (hadj : (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Adj (slotSplitVertex h x) u) :
    ∃ y : TwoPointVertex T, u = slotSplitVertex h y := by
  obtain ⟨hne, leg, hleg, hpartner⟩ := hadj
  obtain ⟨z, rfl⟩ := (slotLegSplitting h).surjective leg
  cases z with
  | inl i =>
      refine ⟨twoPointVertexOfLeg (ext.pairing.partner i), ?_⟩
      rw [TwoPointDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
        twoPointVertexOfLeg_slotLegSplitting_inl] at hpartner
      exact hpartner.symm
  | inr j =>
      obtain ⟨w, hw, hvert⟩ :=
        exists_not_mem_twoPointVertexOfLeg_slotLegSplitting_inr h j
      exact absurd (hvert.symm.trans hleg).symm (slotSplitVertex_ne_inr_of_not_mem h x hw)

/-- The external piece maps into the reassembled diagram as a graph homomorphism. -/
noncomputable def ofSlotSplitHom :
    ext.vertexGraph →g (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph where
  toFun := slotSplitVertex h
  map_rel' := fun {_ _} hab =>
    (adj_ofSlotSplit_slotSplitVertex_iff h ext vac _ _).2 hab

/-- Reachability inside the external piece survives reassembly. -/
theorem reachable_ofSlotSplit_of_reachable {x y : TwoPointVertex T}
    (hreach : ext.vertexGraph.Reachable x y) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      (slotSplitVertex h x) (slotSplitVertex h y) := by
  exact hreach.map (ofSlotSplitHom h ext vac)

/-- **Every walk of a reassembled diagram starting in the external piece stays in it**, and its
image is a walk of that piece. -/
theorem exists_reachable_of_walk_ofSlotSplit :
    ∀ {u v : TwoPointVertex S},
      (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Walk u v →
        ∀ x : TwoPointVertex T, u = slotSplitVertex h x →
          ∃ y : TwoPointVertex T, v = slotSplitVertex h y ∧ ext.vertexGraph.Reachable x y := by
  intro u v p
  induction p with
  | nil => exact fun x hx => ⟨x, hx, SimpleGraph.Reachable.refl _⟩
  | cons hadj p ih =>
      intro x hx
      subst hx
      obtain ⟨x', hx'⟩ := exists_eq_slotSplitVertex_of_adj h ext vac hadj
      obtain ⟨y, hy, hreach⟩ := ih x' hx'
      refine ⟨y, hy, SimpleGraph.Reachable.trans ?_ hreach⟩
      exact (SimpleGraph.Adj.reachable
        ((adj_ofSlotSplit_slotSplitVertex_iff h ext vac x x').1 (hx' ▸ hadj)))

/-- Reachability from a vertex of the external piece is reachability inside that piece. -/
theorem reachable_ofSlotSplit_iff (x y : TwoPointVertex T) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (slotSplitVertex h x) (slotSplitVertex h y) ↔
      ext.vertexGraph.Reachable x y := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨y', hy', hreach⟩ := exists_reachable_of_walk_ofSlotSplit h ext vac p x rfl
    have : y = y' := slotSplitVertex_injective h hy'
    exact this ▸ hreach
  · exact reachable_ofSlotSplit_of_reachable h ext vac

/-- **The slot set of a reassembled diagram is its external component's interaction part**, provided
the external piece really is externally connected. -/
theorem interactionPart_externalComponent_ofSlotSplit
    (hext : ext.IsExternallyConnected) :
    TwoPointDiagram.interactionPart
        ((TwoPointDiagram.ofSlotSplit h ext vac).externalComponent 0) = T := by
  classical
  ext v
  rw [TwoPointDiagram.mem_interactionPart]
  constructor
  · rintro ⟨hv, hmem⟩
    have hreach :=
      ((TwoPointDiagram.ofSlotSplit h ext vac).mem_componentBlock
        (Sum.inl 0) (Sum.inr ⟨v, hv⟩)).1 hmem
    obtain ⟨y, hy, -⟩ :=
      exists_reachable_of_walk_ofSlotSplit h ext vac hreach.symm.some (Sum.inl 0) rfl
    cases y with
    | inl e => simp [slotSplitVertex] at hy
    | inr w =>
        have hEq : (⟨v, hv⟩ : ↥S) = ⟨w.1, h w.2⟩ := by
          simpa [slotSplitVertex] using hy
        have hvw : v = (w : Fin N) := congrArg Subtype.val hEq
        rw [hvw]
        exact w.2
  · intro hvT
    refine ⟨h hvT, ?_⟩
    obtain ⟨e, he⟩ := hext.1 ⟨v, hvT⟩
    have hmapped :
        (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
          (Sum.inl e) (Sum.inr ⟨v, h hvT⟩) := by
      simpa [slotSplitVertex] using reachable_ofSlotSplit_of_reachable h ext vac he
    have hexternal :
        (TwoPointDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
          (Sum.inl e) (Sum.inl 0) := by
      fin_cases e
      · exact SimpleGraph.Reachable.refl _
      · exact (TwoPointDiagram.ofSlotSplit h ext vac).externalVerticesConnected.symm
    exact ((TwoPointDiagram.ofSlotSplit h ext vac).mem_componentBlock
      (Sum.inl 0) (Sum.inr ⟨v, h hvT⟩)).2 (hmapped.symm.trans hexternal)

/-- A diagram whose external component has interaction part `T` is split by the corresponding slot
leg splitting. -/
theorem isSplit_slotLegSplitting_of_interactionPart_eq
    {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (hd : TwoPointDiagram.interactionPart (d.externalComponent 0) = T) :
    d.pairing.IsSplit (slotLegSplitting h) := by
  subst hd
  exact d.isSplit_externalSlotLegSplitting

/-- **The external piece of such a diagram is externally connected.** -/
theorem isExternallyConnected_slotSplitExternal
    {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (hd : TwoPointDiagram.interactionPart (d.externalComponent 0) = T)
    (hsplit : d.pairing.IsSplit (slotLegSplitting h)) :
    (d.slotSplitExternal h hsplit).IsExternallyConnected := by
  rw [TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent]
  intro v
  refine ⟨0, ?_⟩
  have hvT : (v : Fin N) ∈ TwoPointDiagram.interactionPart (d.externalComponent 0) := by
    rw [hd]
    exact v.2
  have hmem : (Sum.inr ⟨v.1, h v.2⟩ : TwoPointVertex S) ∈ d.externalComponent 0 :=
    (TwoPointDiagram.mem_interactionPart_subtype (d.externalComponent 0) ⟨v.1, h v.2⟩).1 hvT
  have hreach : d.vertexGraph.Reachable (Sum.inr ⟨v.1, h v.2⟩) (Sum.inl 0) :=
    (d.mem_componentBlock (Sum.inl 0) (Sum.inr ⟨v.1, h v.2⟩)).1 hmem
  have hD : TwoPointDiagram.ofSlotSplit h (d.slotSplitExternal h hsplit)
      (d.slotSplitVacuum h hsplit) = d :=
    TwoPointDiagram.ofSlotSplit_slotSplit h d hsplit
  have hreach' : (TwoPointDiagram.ofSlotSplit h (d.slotSplitExternal h hsplit)
      (d.slotSplitVacuum h hsplit)).vertexGraph.Reachable
        (slotSplitVertex h (Sum.inl 0)) (slotSplitVertex h (Sum.inr v)) := by
    rw [hD]
    simpa [slotSplitVertex] using hreach.symm
  exact (reachable_ofSlotSplit_iff h _ _ (Sum.inl 0) (Sum.inr v)).1 hreach'

/-- **The fiber decomposition of the diagram sum.**

The diagrams whose external component occupies exactly the interaction vertices `T` are the pairs
consisting of an externally connected two-point diagram on `T` and an arbitrary quartic diagram on
`S \ T`.  This is the statement that lets the linked-cluster factorization organize the sum over
diagrams as a Cauchy product. -/
noncomputable def TwoPointDiagram.externalFiberEquiv :
    {d : TwoPointDiagram ExternalLabel InternalLabel N S //
        TwoPointDiagram.interactionPart (d.externalComponent 0) = T} ≃
      {ext : TwoPointDiagram ExternalLabel InternalLabel N T // ext.IsExternallyConnected} ×
        QuarticDiagram InternalLabel N (S \ T) where
  toFun d :=
    (⟨d.1.slotSplitExternal h (isSplit_slotLegSplitting_of_interactionPart_eq h d.2),
        isExternallyConnected_slotSplitExternal h d.2 _⟩,
      d.1.slotSplitVacuum h (isSplit_slotLegSplitting_of_interactionPart_eq h d.2))
  invFun p :=
    ⟨TwoPointDiagram.ofSlotSplit h p.1.1 p.2,
      interactionPart_externalComponent_ofSlotSplit h p.1.1 p.2 p.1.2⟩
  left_inv d :=
    Subtype.ext (TwoPointDiagram.ofSlotSplit_slotSplit h d.1
      (isSplit_slotLegSplitting_of_interactionPart_eq h d.2))
  right_inv p := by
    obtain ⟨⟨ext, hext⟩, vac⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨Subtype.ext ?_, ?_⟩
    · exact TwoPointDiagram.slotSplitExternal_ofSlotSplit h ext vac _
    · exact TwoPointDiagram.slotSplitVacuum_ofSlotSplit h ext vac _

end Common
end SecondQuantization
