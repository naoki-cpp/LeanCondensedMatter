import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportDecomposition

set_option linter.style.header false

/-!
# Vacuum-freeness of the canonical external-support diagram

The slot splitting preserves and reflects reachability between vertices on its external-bearing
side. Hence restricting a diagram to all components meeting the external sector leaves no vacuum
components, without requiring distinct external vertices to be mutually connected.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}
  {S T : Finset (Fin N)}

/-- Embed external-bearing vertices into the ambient vertex type of a slot split. -/
private def supportSlotVertex (h : T ⊆ S) :
    ExternalInsertionVertex E T → ExternalInsertionVertex E S
  | Sum.inl e => Sum.inl e
  | Sum.inr v => Sum.inr ⟨v.1, h v.2⟩

private theorem supportSlotVertex_injective (h : T ⊆ S) :
    Function.Injective (supportSlotVertex (E := E) h) := by
  rintro (e | v) (f | w) heq
  · simpa [supportSlotVertex] using heq
  · simp [supportSlotVertex] at heq
  · simp [supportSlotVertex] at heq
  · simp only [supportSlotVertex, Sum.inr.injEq, Subtype.mk.injEq] at heq
    exact congrArg Sum.inr (Subtype.ext heq)

private theorem supportSlotVertex_ne_inr_of_not_mem
    (h : T ⊆ S) (x : ExternalInsertionVertex E T) {w : ↥S}
    (hw : (w : Fin N) ∉ T) :
    supportSlotVertex h x ≠ Sum.inr w := by
  cases x with
  | inl e => simp [supportSlotVertex]
  | inr v =>
      simp only [supportSlotVertex, ne_eq, Sum.inr.injEq, Subtype.ext_iff]
      intro heq
      exact hw (heq ▸ v.2)

private theorem supportSlotVertex_of_left_leg (h : T ⊆ S)
    (i : Fin (2 * (2 * T.card + E))) :
    externalInsertionVertexOfLeg
        (externalInsertionSlotLegSplitting (E := E) h (Sum.inl i)) =
      supportSlotVertex h (externalInsertionVertexOfLeg i) := by
  obtain ⟨x, rfl⟩ := (externalInsertionLegEquiv E T).symm.surjective i
  cases x with
  | inl e =>
      rw [externalInsertionSlotLegSplitting_external]
      simp [externalInsertionVertexOfLeg, supportSlotVertex]
  | inr p =>
      obtain ⟨v, l⟩ := p
      rw [externalInsertionSlotLegSplitting_left_interaction]
      simp [externalInsertionVertexOfLeg, supportSlotVertex]

private theorem supportSlotVertex_of_right_leg (h : T ⊆ S)
    (i : Fin (2 * (2 * (S \ T).card))) :
    ∃ w : ↥S, (w : Fin N) ∉ T ∧
      externalInsertionVertexOfLeg
        (externalInsertionSlotLegSplitting (E := E) h (Sum.inr i)) = Sum.inr w := by
  obtain ⟨p, rfl⟩ := (quarticLegEquiv (S \ T)).symm.surjective i
  obtain ⟨v, l⟩ := p
  refine ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, (Finset.mem_sdiff.mp v.2).2, ?_⟩
  rw [externalInsertionSlotLegSplitting_right_interaction]
  simp [externalInsertionVertexOfLeg]

variable (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))

private theorem supportSlotVertex_adj_iff (x y : ExternalInsertionVertex E T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
        (supportSlotVertex h x) (supportSlotVertex h y) ↔
      ext.vertexGraph.Adj x y := by
  constructor
  · rintro ⟨hne, leg, hleg, hpartner⟩
    obtain ⟨z, rfl⟩ := (externalInsertionSlotLegSplitting (E := E) h).surjective leg
    cases z with
    | inl i =>
        rw [supportSlotVertex_of_left_leg] at hleg
        rw [ExternalInsertionDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
          supportSlotVertex_of_left_leg] at hpartner
        refine ⟨fun hxy => hne (congrArg (supportSlotVertex h) hxy), i,
          supportSlotVertex_injective h hleg, supportSlotVertex_injective h hpartner⟩
    | inr j =>
        obtain ⟨w, hw, hvert⟩ := supportSlotVertex_of_right_leg h j
        exact absurd (hvert.symm.trans hleg).symm
          (supportSlotVertex_ne_inr_of_not_mem h x hw)
  · rintro ⟨hne, i, hi, hpartner⟩
    refine ⟨fun heq => hne (supportSlotVertex_injective h heq),
      externalInsertionSlotLegSplitting (E := E) h (Sum.inl i), ?_, ?_⟩
    · rw [supportSlotVertex_of_left_leg, hi]
    · rw [ExternalInsertionDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
        supportSlotVertex_of_left_leg, hpartner]

private theorem supportSlotVertex_exists_of_adj
    {x : ExternalInsertionVertex E T} {u : ExternalInsertionVertex E S}
    (hadj : (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Adj
      (supportSlotVertex h x) u) :
    ∃ y : ExternalInsertionVertex E T, u = supportSlotVertex h y := by
  obtain ⟨-, leg, hleg, hpartner⟩ := hadj
  obtain ⟨z, rfl⟩ := (externalInsertionSlotLegSplitting (E := E) h).surjective leg
  cases z with
  | inl i =>
      refine ⟨externalInsertionVertexOfLeg (ext.pairing.partner i), ?_⟩
      rw [ExternalInsertionDiagram.ofSlotSplit_pairing, Pairing.ofSplit_partner_inl,
        supportSlotVertex_of_left_leg] at hpartner
      exact hpartner.symm
  | inr j =>
      obtain ⟨w, hw, hvert⟩ := supportSlotVertex_of_right_leg h j
      exact absurd (hvert.symm.trans hleg).symm
        (supportSlotVertex_ne_inr_of_not_mem h x hw)

private noncomputable def supportSlotVertexHom :
    ext.vertexGraph →g (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph where
  toFun := supportSlotVertex h
  map_rel' := fun {_ _} hadj =>
    (supportSlotVertex_adj_iff h ext vac _ _).2 hadj

private theorem supportSlotVertex_reachable_of_reachable
    {x y : ExternalInsertionVertex E T}
    (hreach : ext.vertexGraph.Reachable x y) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
      (supportSlotVertex h x) (supportSlotVertex h y) :=
  hreach.map (supportSlotVertexHom h ext vac)

private theorem supportSlotVertex_walk_lift :
    ∀ {u v : ExternalInsertionVertex E S},
      (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Walk u v →
        ∀ x : ExternalInsertionVertex E T, u = supportSlotVertex h x →
          ∃ y : ExternalInsertionVertex E T,
            v = supportSlotVertex h y ∧ ext.vertexGraph.Reachable x y := by
  intro u v walk
  induction walk with
  | nil => exact fun x hx => ⟨x, hx, SimpleGraph.Reachable.refl _⟩
  | cons hadj walk ih =>
      intro x hx
      subst hx
      obtain ⟨x', hx'⟩ := supportSlotVertex_exists_of_adj h ext vac hadj
      obtain ⟨y, hy, hreach⟩ := ih x' hx'
      refine ⟨y, hy, SimpleGraph.Reachable.trans ?_ hreach⟩
      exact SimpleGraph.Adj.reachable
        ((supportSlotVertex_adj_iff h ext vac x x').1 (hx' ▸ hadj))

private theorem supportSlotVertex_reachable_iff (x y : ExternalInsertionVertex E T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (supportSlotVertex h x) (supportSlotVertex h y) ↔
      ext.vertexGraph.Reachable x y := by
  constructor
  · rintro ⟨walk⟩
    obtain ⟨y', hy', hreach⟩ :=
      supportSlotVertex_walk_lift h ext vac walk x rfl
    have heq : y = y' := supportSlotVertex_injective h hy'
    exact heq ▸ hreach
  · exact supportSlotVertex_reachable_of_reachable h ext vac

/-- The canonical external-bearing diagram contains no pure-vacuum connected components.
All components touching distinct external insertions are retained independently. -/
theorem ExternalInsertionDiagram.hasNoVacuumComponent_externalSupportDiagram
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    HasNoVacuumComponent d.externalSupportDiagram.vertexGraph := by
  classical
  intro v
  let T := d.externallySupportedInteractionPart
  let h : T ⊆ S := d.externallySupportedInteractionPart_subset
  let ext := d.externalSupportDiagram
  let vac := d.vacuumComplementDiagram
  let vS : ↥S := ⟨v.1, h v.2⟩
  obtain ⟨e, he⟩ := (d.mem_externallySupportedInteractionPart vS).1 v.2
  have hreach : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) :=
    (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).1 he
  have hD : ExternalInsertionDiagram.ofSlotSplit h ext vac = d :=
    d.externalSupport_reconstruction
  have hreach' :
      (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
        (supportSlotVertex h (Sum.inl e))
        (supportSlotVertex h (Sum.inr v)) := by
    rw [hD]
    simpa [supportSlotVertex] using hreach
  exact ⟨e, (supportSlotVertex_reachable_iff h ext vac (Sum.inl e) (Sum.inr v)).1
    hreach'⟩


/-- Reassembling a vacuum-free external-bearing diagram with an arbitrary quartic complement
has exactly the chosen external-support interaction slots. No connectivity between distinct
external components is assumed. -/
theorem ExternalInsertionDiagram.externallySupportedInteractionPart_ofSlotSplit
    (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \\ T))
    (hext : HasNoVacuumComponent ext.vertexGraph) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).externallySupportedInteractionPart = T := by
  classical
  let d := ExternalInsertionDiagram.ofSlotSplit h ext vac
  apply Finset.Subset.antisymm d.externallySupportedInteractionPart_subset
  · intro v hv
    have hvS : v ∈ S := d.externallySupportedInteractionPart_subset hv
    let vS : ↥S := ⟨v, hvS⟩
    obtain ⟨e, he⟩ := (d.mem_externallySupportedInteractionPart vS).1 hv
    have hr : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) :=
      (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).1 he
    have hr' :
        (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexGraph.Reachable
          (supportSlotVertex h (Sum.inl e)) (Sum.inr vS) := by
      simpa [d, supportSlotVertex] using hr
    obtain ⟨y, hy, -⟩ :=
      supportSlotVertex_walk_lift h ext vac hr'.some (Sum.inl e) rfl
    cases y with
    | inl f => simp [supportSlotVertex] at hy
    | inr w =>
        have heq : v = (w : Fin N) := by
          simpa [supportSlotVertex] using hy
        exact heq ▸ w.2
  · intro v hv
    let vT : ↥T := ⟨v, hv⟩
    let vS : ↥S := ⟨v, h hv⟩
    obtain ⟨e, he⟩ := hext vT
    have hr : d.vertexGraph.Reachable (Sum.inl e) (Sum.inr vS) := by
      have hmapped := supportSlotVertex_reachable_of_reachable h ext vac he
      simpa [d, supportSlotVertex] using hmapped
    apply (d.mem_externallySupportedInteractionPart vS).2
    exact ⟨e, (d.vertexGraph.mem_componentBlock (Sum.inr vS) (Sum.inl e)).2 hr⟩

end Common
end SecondQuantization
