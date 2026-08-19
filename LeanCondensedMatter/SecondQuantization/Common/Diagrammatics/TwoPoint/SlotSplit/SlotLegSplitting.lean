import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Leg
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Diagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.SubsetSplit

set_option linter.style.header false

/-!
# The leg splitting determined by a choice of interaction vertices

Choosing a subset `T` of the interaction vertices splits the ambient legs of a two-point diagram in
two: the two external legs together with the four legs of every vertex of `T`, and the four legs of
every vertex of `S \ T`.

This depends on `T` alone, not on any diagram. That is what distinguishes it from
`TwoPointDiagram.legPositionSplitting`, which is read off a diagram's component structure and can
therefore only take a diagram apart. Reconstructing a diagram from an external piece and a vacuum
piece needs the splitting to exist first, and this is it.

The two are related by instantiating `T` at the external component's interaction vertices.

Reconstruction and decomposition along such a splitting are mutually inverse, so the diagrams whose
pairing does not cross the divide are exactly the pairs of pieces (`TwoPointDiagram.slotSplitEquiv`).
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {N : ℕ}

/-- The ambient legs presented as the legs of `T` — including the two external legs — together with
the legs of `S \ T`. -/
noncomputable def slotLegSplitting {S : Finset (Fin N)} {T : Finset (Fin N)} (h : T ⊆ S) :
    Combinatorics.PositionSplitting (2 * T.card + 1) (2 * (S \ T).card) (2 * S.card + 1) :=
  (Equiv.sumCongr (twoPointLegEquiv T) (quarticLegEquiv (S \ T))).trans
    (((Equiv.sumAssoc (Fin 2) (↥T × Fin 4) (↥(S \ T) × Fin 4)).trans
      (Equiv.sumCongr (Equiv.refl (Fin 2))
        ((Equiv.sumProdDistrib (↥T) (↥(S \ T)) (Fin 4)).symm.trans
          (Equiv.prodCongr (Combinatorics.subsetSumSdiffEquiv h) (Equiv.refl (Fin 4)))))).trans
      (twoPointLegEquiv S).symm)

/-- External legs land on the left part. -/
@[simp]
theorem slotLegSplitting_external {S T : Finset (Fin N)} (h : T ⊆ S) (e : Fin 2) :
    slotLegSplitting h (Sum.inl ((twoPointLegEquiv T).symm (Sum.inl e))) =
      (twoPointLegEquiv S).symm (Sum.inl e) := by
  simp [slotLegSplitting]

/-- A left interaction leg lands on the corresponding ambient leg. -/
@[simp]
theorem slotLegSplitting_left_interaction {S T : Finset (Fin N)} (h : T ⊆ S)
    (v : ↥T) (l : Fin 4) :
    slotLegSplitting h (Sum.inl ((twoPointLegEquiv T).symm (Sum.inr (v, l)))) =
      (twoPointLegEquiv S).symm (Sum.inr (⟨v.1, h v.2⟩, l)) := by
  simp [slotLegSplitting, Combinatorics.subsetSumSdiffEquiv]

/-- A right interaction leg lands on the corresponding ambient leg. -/
@[simp]
theorem slotLegSplitting_right_interaction {S T : Finset (Fin N)} (h : T ⊆ S)
    (v : ↥(S \ T)) (l : Fin 4) :
    slotLegSplitting h (Sum.inr ((quarticLegEquiv (S \ T)).symm (v, l))) =
      (twoPointLegEquiv S).symm
        (Sum.inr (⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, l)) := by
  simp [slotLegSplitting, Combinatorics.subsetSumSdiffEquiv]

variable {ExternalLabel InternalLabel : Type*}

/-- **Reconstruct a two-point diagram from an external piece and a vacuum piece.**

The external labels come from the external piece, each vertex label is read off whichever side its
vertex belongs to, and the pairing is assembled by `Pairing.ofSplit` along `slotLegSplitting`.

Nothing here inspects connectivity: the vacuum piece may be disconnected, and the external piece is
not required to be externally connected. Those conditions belong to the statement that this is
inverse to the decomposition, not to the construction. -/
noncomputable def TwoPointDiagram.ofSlotSplit {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) :
    TwoPointDiagram ExternalLabel InternalLabel N S where
  externalLabel := ext.externalLabel
  vertexLabel v :=
    if hv : (v : Fin N) ∈ T then ext.vertexLabel ⟨v, hv⟩
    else vac.vertexLabel ⟨v, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩
  pairing := Pairing.ofSplit (slotLegSplitting h) ext.pairing vac.pairing

@[simp]
theorem TwoPointDiagram.ofSlotSplit_externalLabel {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) (e : Fin 2) :
    (TwoPointDiagram.ofSlotSplit h ext vac).externalLabel e = ext.externalLabel e :=
  rfl

@[simp]
theorem TwoPointDiagram.ofSlotSplit_pairing {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) :
    (TwoPointDiagram.ofSlotSplit h ext vac).pairing =
      Pairing.ofSplit (slotLegSplitting h) ext.pairing vac.pairing :=
  rfl

theorem TwoPointDiagram.ofSlotSplit_vertexLabel_of_mem {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) (v : ↥S) (hv : (v : Fin N) ∈ T) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel v = ext.vertexLabel ⟨v, hv⟩ :=
  dif_pos hv

theorem TwoPointDiagram.ofSlotSplit_vertexLabel_of_not_mem {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) (v : ↥S) (hv : (v : Fin N) ∉ T) :
    (TwoPointDiagram.ofSlotSplit h ext vac).vertexLabel v =
      vac.vertexLabel ⟨v, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ :=
  dif_neg hv

section Decompose

variable {S T : Finset (Fin N)}

/-- The external piece of a diagram whose pairing is split by the slot leg splitting: the vertices
of `T`, the two external legs, and the pairing they carry. -/
noncomputable def TwoPointDiagram.slotSplitExternal (h : T ⊆ S)
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hd : d.pairing.IsSplit (slotLegSplitting h)) :
    TwoPointDiagram ExternalLabel InternalLabel N T where
  externalLabel := d.externalLabel
  vertexLabel v := d.vertexLabel ⟨v.1, h v.2⟩
  pairing := d.pairing.splitLeft (slotLegSplitting h) hd

/-- The vacuum piece of a diagram whose pairing is split by the slot leg splitting: the vertices of
`S \ T` and the pairing they carry, as an ordinary quartic diagram. -/
noncomputable def TwoPointDiagram.slotSplitVacuum (h : T ⊆ S)
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hd : d.pairing.IsSplit (slotLegSplitting h)) :
    QuarticDiagram InternalLabel N (S \ T) where
  vertexLabel v := d.vertexLabel ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩
  pairing := d.pairing.splitRight (slotLegSplitting h) hd

/-- **Taking a diagram apart and putting it back returns the diagram.** -/
theorem TwoPointDiagram.ofSlotSplit_slotSplit (h : T ⊆ S)
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hd : d.pairing.IsSplit (slotLegSplitting h)) :
    TwoPointDiagram.ofSlotSplit h (d.slotSplitExternal h hd) (d.slotSplitVacuum h hd) = d := by
  refine TwoPointDiagram.ext rfl (funext fun v => ?_) ?_
  · by_cases hv : (v : Fin N) ∈ T
    · exact TwoPointDiagram.ofSlotSplit_vertexLabel_of_mem h _ _ v hv
    · exact TwoPointDiagram.ofSlotSplit_vertexLabel_of_not_mem h _ _ v hv
  · exact Pairing.ofSplit_splitLeft_splitRight (slotLegSplitting h) hd

/-- A reconstructed diagram is split by the splitting it was reconstructed along. -/
theorem TwoPointDiagram.isSplit_ofSlotSplit (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) :
    (TwoPointDiagram.ofSlotSplit h ext vac).pairing.IsSplit (slotLegSplitting h) :=
  Pairing.isSplit_ofSplit _ _ _

/-- Reconstructing and then reading off the external piece returns the external piece. -/
theorem TwoPointDiagram.slotSplitExternal_ofSlotSplit (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hd : (TwoPointDiagram.ofSlotSplit h ext vac).pairing.IsSplit (slotLegSplitting h)) :
    (TwoPointDiagram.ofSlotSplit h ext vac).slotSplitExternal h hd = ext := by
  refine TwoPointDiagram.ext rfl (funext fun v => ?_) ?_
  · exact TwoPointDiagram.ofSlotSplit_vertexLabel_of_mem h ext vac ⟨v.1, h v.2⟩ v.2
  · exact Pairing.splitLeft_ofSplit (slotLegSplitting h) ext.pairing vac.pairing

/-- Reconstructing and then reading off the vacuum piece returns the vacuum piece. -/
theorem TwoPointDiagram.slotSplitVacuum_ofSlotSplit (h : T ⊆ S)
    (ext : TwoPointDiagram ExternalLabel InternalLabel N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hd : (TwoPointDiagram.ofSlotSplit h ext vac).pairing.IsSplit (slotLegSplitting h)) :
    (TwoPointDiagram.ofSlotSplit h ext vac).slotSplitVacuum h hd = vac := by
  refine QuarticDiagram.ext (funext fun v => ?_) ?_
  · exact TwoPointDiagram.ofSlotSplit_vertexLabel_of_not_mem h ext vac
      ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ (Finset.mem_sdiff.mp v.2).2
  · exact Pairing.splitRight_ofSplit (slotLegSplitting h) ext.pairing vac.pairing

/-- **The diagrams split by a slot leg splitting are exactly the pairs of pieces.**

The reindexing engine of the binary external/vacuum decomposition: summing over two-point diagrams
on `S` whose pairing does not cross the divide is summing over an external diagram on `T` and a
vacuum diagram on `S \ T` independently.

Nothing here mentions connectivity. Connectivity enters only in identifying which `T` a given
diagram is split by, namely its external component's interaction vertices. -/
noncomputable def TwoPointDiagram.slotSplitEquiv (h : T ⊆ S) :
    {d : TwoPointDiagram ExternalLabel InternalLabel N S //
        d.pairing.IsSplit (slotLegSplitting h)} ≃
      TwoPointDiagram ExternalLabel InternalLabel N T × QuarticDiagram InternalLabel N (S \ T) where
  toFun d := (d.1.slotSplitExternal h d.2, d.1.slotSplitVacuum h d.2)
  invFun p :=
    ⟨TwoPointDiagram.ofSlotSplit h p.1 p.2, TwoPointDiagram.isSplit_ofSlotSplit h p.1 p.2⟩
  left_inv d := Subtype.ext (TwoPointDiagram.ofSlotSplit_slotSplit h d.1 d.2)
  right_inv p := by
    obtain ⟨ext, vac⟩ := p
    simp only [Prod.mk.injEq]
    exact ⟨TwoPointDiagram.slotSplitExternal_ofSlotSplit h ext vac _,
      TwoPointDiagram.slotSplitVacuum_ofSlotSplit h ext vac _⟩

open Classical in
/-- **Summing over split diagrams is summing over the two pieces independently.**

The reindexing the binary external/vacuum factorization runs on: it turns one sum over diagrams into
a double sum whose inner factors are supported on disjoint slot blocks, which is the shape the
binary ordered-simplex shuffle identity consumes. -/
theorem TwoPointDiagram.sum_slotSplit [Fintype ExternalLabel] [Fintype InternalLabel]
    (h : T ⊆ S) {M : Type*} [AddCommMonoid M]
    (F : TwoPointDiagram ExternalLabel InternalLabel N S → M) :
    (∑ d : {d : TwoPointDiagram ExternalLabel InternalLabel N S //
        d.pairing.IsSplit (slotLegSplitting h)}, F d.1) =
      ∑ ext : TwoPointDiagram ExternalLabel InternalLabel N T,
        ∑ vac : QuarticDiagram InternalLabel N (S \ T),
          F (TwoPointDiagram.ofSlotSplit h ext vac) := by
  rw [← Equiv.sum_comp (TwoPointDiagram.slotSplitEquiv h).symm (fun d => F d.1),
    Fintype.sum_prod_type]
  rfl

end Decompose

end Common
end SecondQuantization
