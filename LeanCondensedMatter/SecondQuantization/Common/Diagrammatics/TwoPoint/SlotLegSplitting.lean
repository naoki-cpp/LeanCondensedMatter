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

end Common
end SecondQuantization
