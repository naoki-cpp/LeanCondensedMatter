import LeanCondensedMatter.Combinatorics.FamilySlotShuffleSign
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentMixedCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Perm.Sign

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


private noncomputable def sigmaFiberEquiv
    {ι : Type*} {β : ι → Type*} (i : ι) :
    β i ≃ {x : Σ j, β j // x.1 = i} where
  toFun x := ⟨⟨i, x⟩, rfl⟩
  invFun x := by
    rcases x with ⟨⟨j, x⟩, h⟩
    have hji : j = i := h
    subst j
    exact x
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨⟨j, x⟩, h⟩
    have hji : j = i := h
    subst j
    rfl

private theorem sign_sigmaCongrRight_mulSingle
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (i : ι) (p : Equiv.Perm (β i)) :
    Equiv.Perm.sign (Equiv.sigmaCongrRight (Pi.mulSingle i p)) =
      Equiv.Perm.sign p := by
  classical
  have hperm :
      Equiv.sigmaCongrRight (Pi.mulSingle i p) =
        p.extendDomain (sigmaFiberEquiv i) := by
    apply Equiv.ext
    rintro ⟨j, x⟩
    by_cases hji : j = i
    · subst j
      rw [Equiv.Perm.extendDomain_apply_subtype _ _ rfl]
      simp [sigmaFiberEquiv, Pi.mulSingle_apply]
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simpa using hji)]
      simp [Pi.mulSingle_apply, hji]
  rw [hperm, Equiv.Perm.sign_extendDomain]

private theorem sign_sigmaCongrRight_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (p : ∀ i, Equiv.Perm (β i)) :
    Equiv.Perm.sign (Equiv.sigmaCongrRight p) =
      ∏ i, Equiv.Perm.sign (p i) := by
  classical
  let hcomm :
      Pairwise fun i j : ι =>
        ∀ (x : Equiv.Perm (β i)) (y : Equiv.Perm (β j)),
          Commute (Equiv.Perm.sign x) (Equiv.Perm.sign y) :=
    fun _ _ _ _ _ => Commute.all _ _
  let rhs : (∀ i, Equiv.Perm (β i)) →* ℤˣ :=
    MonoidHom.noncommPiCoprod (fun i => Equiv.Perm.sign) hcomm
  have hhom :
      Equiv.Perm.sign.comp (Equiv.Perm.sigmaCongrRightHom β) = rhs := by
    apply MonoidHom.pi_ext
    intro i q
    change Equiv.Perm.sign (Equiv.sigmaCongrRight (Pi.mulSingle i q)) =
      rhs (Pi.mulSingle i q)
    rw [sign_sigmaCongrRight_mulSingle i q]
    simp [rhs, MonoidHom.noncommPiCoprod_mulSingle]
  have hp := congrArg (fun h : (∀ i, Equiv.Perm (β i)) →* ℤˣ => h p) hhom
  change Equiv.Perm.sign (Equiv.sigmaCongrRight p) = rhs p at hp
  dsimp [rhs] at hp
  rw [MonoidHom.noncommPiCoprod_apply, Finset.noncommProd_eq_prod] at hp
  exact hp

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


private theorem ExternalInsertionWickDiagram.componentMixedToFixedPositionEquiv_sign
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (B : d.vertexGraph.componentPartition.parts) :
    Equiv.Perm.sign (d.componentMixedToFixedPositionEquiv externalTime σ B) =
      Equiv.Perm.sign
        (externalInsertionStandardToMixedAtomicPositionEquiv
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)) := by
  have hperm :
      d.componentMixedToFixedPositionEquiv externalTime σ B =
        (externalInsertionStandardToMixedAtomicPositionEquiv
          (d.componentExternalTime externalTime B)
          (d.componentInteractionTime σ B)).symm := by
    apply Equiv.ext
    intro p
    apply Fin.ext
    rfl
  rw [hperm, Equiv.Perm.sign_symm]

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
  let localPerm := fun B : d.vertexGraph.componentPartition.parts =>
    d.componentMixedToFixedPositionEquiv externalTime σ B
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
    sign_sigmaCongrRight_eq_prod]
  change Equiv.Perm.sign globalPerm *
      (∏ B : d.vertexGraph.componentPartition.parts,
        Equiv.Perm.sign (localPerm B)) =
    Equiv.Perm.sign globalPerm * _
  congr 1
  apply Finset.prod_congr rfl
  intro B _
  exact d.componentMixedToFixedPositionEquiv_sign externalTime σ B


end Fermionic
end SecondQuantization
