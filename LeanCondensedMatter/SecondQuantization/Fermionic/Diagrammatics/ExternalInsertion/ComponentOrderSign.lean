import LeanCondensedMatter.Combinatorics.FamilySlotShuffleSign
import LeanCondensedMatter.Combinatorics.SigmaPermutationSign
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentMixedCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign

set_option linter.style.header false

/-!
# Mixed/fixed component shuffle signs for arbitrary external insertions

The canonical component decomposition gives two order-preserving family shuffles of the same atomic
legs: one in the fixed flattened order and one in mixed imaginary-time order. This file identifies
the sign of the relative permutation between those shuffles with the product of the fixed external
component regrouping sign and the residual mixed inter-component fermionic crossing sign.
-/

namespace SecondQuantization
namespace Fermionic

open Common Combinatorics
open scoped BigOperators

private theorem orderedBlockInversionCount_castTotalEquiv
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {m n : ℕ}
    (h : m = n) (shuffle : FamilySlotShuffleTo size m)
    (blockOrder : ι ≃ Fin (Fintype.card ι)) :
    (FamilySlotShuffleTo.castTotalEquiv h shuffle).orderedBlockInversionCount blockOrder =
      shuffle.orderedBlockInversionCount blockOrder := by
  subst n
  rfl



variable {Mode : Type*}

/-- Relative permutation from fixed component-local atomic positions to mixed-time component-local
atomic positions. -/
noncomputable def ExternalInsertionWickDiagram.relativeComponentShuffle
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm (Fin (2 * (2 * n + E))) :=
  (FamilySlotShuffleTo.castTotalEquiv
      (m := 2 * (2 * (Finset.univ : Finset (Fin n)).card + E))
      (n := 2 * (2 * n + E)) (by simp) d.componentLegShuffle).relativePerm
    (d.componentMixedPositionShuffle externalTime σ)

/-- The relative permutation between fixed and mixed component shuffles carries exactly the fixed
external regrouping sign and the residual mixed inter-component crossing sign. -/
theorem ExternalInsertionWickDiagram.relativeComponentShuffleSign_eq_external_mul_mixedInter
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (((Equiv.Perm.sign (d.relativeComponentShuffle externalTime σ) : ℤ) : ℂ)) =
      componentExternalOrderSign d blockOrder *
        (Common.Statistics.fermion.zetaInt : ℂ) ^
          d.mixedInterComponentCrossingCount externalTime σ := by
  let fixedShuffle :=
    FamilySlotShuffleTo.castTotalEquiv
      (m := 2 * (2 * (Finset.univ : Finset (Fin n)).card + E))
      (n := 2 * (2 * n + E)) (by simp) d.componentLegShuffle
  change (((Equiv.Perm.sign
    (fixedShuffle.relativePerm
      (d.componentMixedPositionShuffle externalTime σ)) : ℤ) : ℂ)) = _
  rw [FamilySlotShuffleTo.relativePerm_sign_eq_orderedBlockInversionCount_add
    fixedShuffle (d.componentMixedPositionShuffle externalTime σ) blockOrder]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [pow_add]
  unfold componentExternalOrderSign
  have hfixed :
      fixedShuffle.orderedBlockInversionCount blockOrder % 2 =
        d.componentExternalShuffle.orderedBlockInversionCount blockOrder % 2 := by
    rw [orderedBlockInversionCount_castTotalEquiv]
    exact d.componentLegShuffle_orderedBlockInversionCount_mod_two_eq_external blockOrder
  have hmixed :=
    d.mixedInterComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
      externalTime σ blockOrder
  rw [pow_eq_of_mod_two_eq (show ((-1 : ℂ) * -1) = 1 by norm_num) hfixed]
  rw [pow_eq_of_mod_two_eq (show ((-1 : ℂ) * -1) = 1 by norm_num) hmixed.symm]
  simp only [Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]


/-- The relative component shuffle sign is the ambient mixed-time ordering sign times the product
of the component-local mixed-time ordering signs. This is the final permutation-sign bridge needed
to turn mixed-pairing factorization into a fixed-time amplitude factorization. -/
theorem ExternalInsertionWickDiagram.relativeComponentShuffle_sign_eq_mixedAtomic_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    Equiv.Perm.sign (d.relativeComponentShuffle externalTime σ) =
      Equiv.Perm.sign
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) *
        ∏ B : d.vertexGraph.componentPartition.parts,
          Equiv.Perm.sign
            (externalInsertionStandardToMixedAtomicPositionEquiv
              (d.componentExternalTime externalTime B)
              (d.componentInteractionTime σ B)) := by
  classical
  let fixedShuffle :=
    FamilySlotShuffleTo.castTotalEquiv
      (m := 2 * (2 * (Finset.univ : Finset (Fin n)).card + E))
      (n := 2 * (2 * n + E)) (by simp) d.componentLegShuffle
  let globalPerm :=
    externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ
  let localPerm :
      ∀ B : d.vertexGraph.componentPartition.parts,
        Equiv.Perm
          (Fin (2 * (2 * (interactionSector
            (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))).card +
              d.externalPairCount B))) :=
    fun B =>
      (externalInsertionMixedTimeAmbientPositionEquiv
        (d.componentExternalTime externalTime B)
        (d.componentInteractionTime σ B)).trans
        (finCongr (by simp))
  have hmixed :
      (d.componentMixedPositionShuffle externalTime σ).slotEquiv =
        (Equiv.sigmaCongrRight localPerm).trans
          (fixedShuffle.slotEquiv.trans globalPerm) := by
    apply Equiv.ext
    rintro ⟨B, p⟩
    apply Fin.ext
    rfl
  have hrelative :
      d.relativeComponentShuffle externalTime σ =
        ((fixedShuffle.slotEquiv.symm.trans
            (Equiv.sigmaCongrRight localPerm)).trans
          fixedShuffle.slotEquiv).trans globalPerm := by
    unfold ExternalInsertionWickDiagram.relativeComponentShuffle
      FamilySlotShuffleTo.relativePerm
    change fixedShuffle.slotEquiv.symm.trans
        (d.componentMixedPositionShuffle externalTime σ).slotEquiv = _
    rw [hmixed]
    apply Equiv.ext
    intro p
    rfl
  rw [hrelative, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_symm_trans_trans,
    Equiv.Perm.sign_sigmaCongrRight]
  change Equiv.Perm.sign globalPerm *
      (∏ B : d.vertexGraph.componentPartition.parts,
        Equiv.Perm.sign (localPerm B)) =
    Equiv.Perm.sign globalPerm * _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  have hperm :
      localPerm B =
        (externalInsertionStandardToMixedAtomicPositionEquiv
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).symm := by
    apply Equiv.ext
    intro p
    apply Fin.ext
    rfl
  rw [hperm, Equiv.Perm.sign_symm]


end Fermionic
end SecondQuantization
