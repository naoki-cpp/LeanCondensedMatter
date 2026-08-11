import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Leg
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

end Common
end SecondQuantization
