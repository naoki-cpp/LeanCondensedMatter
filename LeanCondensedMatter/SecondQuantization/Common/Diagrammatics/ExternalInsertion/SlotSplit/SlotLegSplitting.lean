import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.SubsetSplit

set_option linter.style.header false

/-!
# Slot splitting for arbitrary external-insertion diagrams

A subset `T` of interaction vertices divides the ambient legs into two sectors: all external
insertions together with the four legs of vertices in `T`, and the four legs of vertices in
`S \ T`.

A pairing that does not cross this split is equivalent to an external-insertion diagram on `T`
and an ordinary quartic diagram on the complementary slots. Connectivity is deliberately absent
from this layer; later consumers choose `T` from externally supported components.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The ambient external-insertion legs presented as the legs of `T`, including every external
leg, together with the quartic legs of `S \ T`. -/
noncomputable def externalInsertionSlotLegSplitting
    {S T : Finset (Fin N)} (h : T ⊆ S) :
    Combinatorics.PositionSplitting
      (2 * (2 * T.card + E))
      (2 * (2 * (S \ T).card))
      (2 * (2 * S.card + E)) :=
  (Equiv.sumCongr (externalInsertionLegEquiv E T) (quarticLegEquiv (S \ T))).trans
    (((Equiv.sumAssoc (Fin (2 * E)) (↥T × Fin 4) (↥(S \ T) × Fin 4)).trans
      (Equiv.sumCongr (Equiv.refl (Fin (2 * E)))
        ((Equiv.sumProdDistrib (↥T) (↥(S \ T)) (Fin 4)).symm.trans
          (Equiv.prodCongr (Combinatorics.subsetSumSdiffEquiv h) (Equiv.refl (Fin 4)))))).trans
      (externalInsertionLegEquiv E S).symm)

/-- External legs land on the left side unchanged. -/
@[simp]
theorem externalInsertionSlotLegSplitting_external
    {S T : Finset (Fin N)} (h : T ⊆ S) (e : Fin (2 * E)) :
    externalInsertionSlotLegSplitting (E := E) h
        (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inl e))) =
      (externalInsertionLegEquiv E S).symm (Sum.inl e) := by
  simp [externalInsertionSlotLegSplitting]

/-- A left interaction leg lands on the corresponding ambient interaction leg. -/
@[simp]
theorem externalInsertionSlotLegSplitting_left_interaction
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (v : ↥T) (l : Fin 4) :
    externalInsertionSlotLegSplitting (E := E) h
        (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inr (v, l)))) =
      (externalInsertionLegEquiv E S).symm
        (Sum.inr (⟨v.1, h v.2⟩, l)) := by
  simp [externalInsertionSlotLegSplitting]

/-- A right quartic leg lands on the corresponding ambient interaction leg. -/
@[simp]
theorem externalInsertionSlotLegSplitting_right_interaction
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (v : ↥(S \ T)) (l : Fin 4) :
    externalInsertionSlotLegSplitting (E := E) h
        (Sum.inr ((quarticLegEquiv (S \ T)).symm (v, l))) =
      (externalInsertionLegEquiv E S).symm
        (Sum.inr (⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, l)) := by
  simp [externalInsertionSlotLegSplitting]

/-- Reconstruct an external-insertion diagram from an external-bearing piece and a quartic
complementary piece. -/
noncomputable def ExternalInsertionDiagram.ofSlotSplit
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N S where
  externalLabel := ext.externalLabel
  vertexLabel v :=
    if hv : (v : Fin N) ∈ T then ext.vertexLabel ⟨v, hv⟩
    else vac.vertexLabel ⟨v, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩
  pairing := Pairing.ofSplit (externalInsertionSlotLegSplitting (E := E) h)
    ext.pairing vac.pairing

@[simp]
theorem ExternalInsertionDiagram.ofSlotSplit_externalLabel
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) (e : Fin (2 * E)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).externalLabel e =
      ext.externalLabel e := rfl

@[simp]
theorem ExternalInsertionDiagram.ofSlotSplit_pairing
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).pairing =
      Pairing.ofSplit (externalInsertionSlotLegSplitting (E := E) h)
        ext.pairing vac.pairing := rfl

theorem ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (v : ↥S) (hv : (v : Fin N) ∈ T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexLabel v =
      ext.vertexLabel ⟨v, hv⟩ := dite_eq_left hv

theorem ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (v : ↥S) (hv : (v : Fin N) ∉ T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexLabel v =
      vac.vertexLabel ⟨v, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ := dite_eq_right hv

section Decompose

variable {S T : Finset (Fin N)}

/-- The external-bearing piece of a diagram whose pairing is split by the chosen interaction slots. -/
noncomputable def ExternalInsertionDiagram.slotSplitExternal
    (h : T ⊆ S)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hd : d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N T where
  externalLabel := d.externalLabel
  vertexLabel v := d.vertexLabel ⟨v.1, h v.2⟩
  pairing := d.pairing.splitLeft (externalInsertionSlotLegSplitting (E := E) h) hd

/-- The complementary vacuum piece as an ordinary quartic diagram. -/
noncomputable def ExternalInsertionDiagram.slotSplitVacuum
    (h : T ⊆ S)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hd : d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)) :
    QuarticDiagram InternalLabel N (S \ T) where
  vertexLabel v := d.vertexLabel ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩
  pairing := d.pairing.splitRight (externalInsertionSlotLegSplitting (E := E) h) hd

/-- Taking a split diagram apart and reassembling it returns the original diagram. -/
theorem ExternalInsertionDiagram.ofSlotSplit_slotSplit
    (h : T ⊆ S)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hd : d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)) :
    ExternalInsertionDiagram.ofSlotSplit h
        (d.slotSplitExternal h hd) (d.slotSplitVacuum h hd) = d := by
  refine ExternalInsertionDiagram.ext rfl (funext fun v => ?_) ?_
  · by_cases hv : (v : Fin N) ∈ T
    · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem h _ _ v hv
    · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem h _ _ v hv
  · exact Pairing.ofSplit_splitLeft_splitRight
      (externalInsertionSlotLegSplitting (E := E) h) hd

/-- Reassembling and reading off the external-bearing piece returns that piece. -/
theorem ExternalInsertionDiagram.slotSplitExternal_ofSlotSplit
    (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hd : (ExternalInsertionDiagram.ofSlotSplit h ext vac).pairing.IsSplit
      (externalInsertionSlotLegSplitting (E := E) h)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).slotSplitExternal h hd = ext := by
  refine ExternalInsertionDiagram.ext rfl (funext fun v => ?_) ?_
  · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem h ext vac
      ⟨v.1, h v.2⟩ v.2
  · exact Pairing.splitLeft_ofSplit
      (externalInsertionSlotLegSplitting (E := E) h) ext.pairing vac.pairing

/-- Reassembling and reading off the quartic complementary piece returns that piece. -/
theorem ExternalInsertionDiagram.slotSplitVacuum_ofSlotSplit
    (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hd : (ExternalInsertionDiagram.ofSlotSplit h ext vac).pairing.IsSplit
      (externalInsertionSlotLegSplitting (E := E) h)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).slotSplitVacuum h hd = vac := by
  refine QuarticDiagram.ext (funext fun v => ?_) ?_
  · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem h ext vac
      ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ (Finset.mem_sdiff.mp v.2).2
  · exact Pairing.splitRight_ofSplit
      (externalInsertionSlotLegSplitting (E := E) h) ext.pairing vac.pairing

/-- Diagrams split by a chosen interaction-slot divide are exactly independent external-insertion
and quartic pieces. -/
noncomputable def ExternalInsertionDiagram.slotSplitEquiv
    (h : T ⊆ S) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)} ≃
      ExternalInsertionDiagram ExternalLabel InternalLabel E N T ×
        QuarticDiagram InternalLabel N (S \ T) where
  toFun d := (d.1.slotSplitExternal h d.2, d.1.slotSplitVacuum h d.2)
  invFun p :=
    ⟨ExternalInsertionDiagram.ofSlotSplit h p.1 p.2,
      Pairing.isSplit_ofSplit _ _ _⟩
  left_inv d := Subtype.ext (ExternalInsertionDiagram.ofSlotSplit_slotSplit h d.1 d.2)
  right_inv p := by
    obtain ⟨ext, vac⟩ := p
    simp only [Prod.mk.injEq]
    exact ⟨ExternalInsertionDiagram.slotSplitExternal_ofSlotSplit h ext vac _,
      ExternalInsertionDiagram.slotSplitVacuum_ofSlotSplit h ext vac _⟩

open Classical in
/-- Summing over split diagrams is summing independently over the external-insertion and quartic
pieces. -/
theorem ExternalInsertionDiagram.sum_slotSplit
    [Fintype ExternalLabel] [Fintype InternalLabel]
    (h : T ⊆ S) {M : Type*} [AddCommMonoid M]
    (F : ExternalInsertionDiagram ExternalLabel InternalLabel E N S → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
        d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)}, F d.1) =
      ∑ ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T,
        ∑ vac : QuarticDiagram InternalLabel N (S \ T),
          F (ExternalInsertionDiagram.ofSlotSplit h ext vac) := by
  rw [← Equiv.sum_comp (ExternalInsertionDiagram.slotSplitEquiv h).symm (fun d => F d.1),
    Fintype.sum_prod_type]
  rfl

end Decompose

end Common
end SecondQuantization
