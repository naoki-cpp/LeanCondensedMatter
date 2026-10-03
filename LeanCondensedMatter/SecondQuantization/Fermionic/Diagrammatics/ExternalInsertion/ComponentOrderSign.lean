import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentMixedCrossing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentSign
import Mathlib.GroupTheory.Perm.Fin

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

private def permInversionCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, if π j < π i then 1 else 0

private theorem ite_lt_eq_neg_one_pow {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    (if a < b then (1 : ℤˣ) else -1) = (-1) ^ (if b < a then 1 else 0) := by
  rcases lt_trichotomy a b with h | h | h
  · rw [ite_eq_left h, ite_eq_right (asymm h), pow_zero]
  · exact absurd h hab
  · rw [ite_eq_right (asymm h), ite_eq_left h, pow_one]

private theorem sign_eq_neg_one_pow_permInversionCount {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign π = (-1 : ℤˣ) ^ permInversionCount π := by
  classical
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  unfold permInversionCount
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  exact ite_lt_eq_neg_one_pow (π i) (π j) (π.injective.ne hij)

private noncomputable def familyRelativePerm {ι : Type*} {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) : Equiv.Perm (Fin total) :=
  σ.slotEquiv.symm.trans τ.slotEquiv

private noncomputable def familyBlockDisagreementCount
    {ι : Type*} {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) (i j : ι) : ℕ :=
  ∑ p : Fin (size i), ∑ q : Fin (size j),
    if σ.slotEquiv ⟨i, p⟩ < σ.slotEquiv ⟨j, q⟩ then
      if τ.slotEquiv ⟨j, q⟩ < τ.slotEquiv ⟨i, p⟩ then 1 else 0
    else 0

private theorem sum_Ioi_eq_sum_ite {m : ℕ} (i : Fin m) (g : Fin m → ℕ) :
    (∑ j ∈ Finset.Ioi i, g j) = ∑ j : Fin m, if i < j then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

private theorem familyRelativePerm_inversionCount_eq_sum_blockDisagreementCount
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) :
    permInversionCount (familyRelativePerm σ τ) =
      ∑ i : ι, ∑ j : ι, familyBlockDisagreementCount σ τ i j := by
  classical
  unfold permInversionCount
  simp_rw [sum_Ioi_eq_sum_ite]
  rw [← Equiv.sum_comp σ.slotEquiv]
  apply Finset.sum_congr rfl
  rintro ⟨i, p⟩ _
  rw [← Equiv.sum_comp σ.slotEquiv]
  simp only [familyRelativePerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [Fintype.sum_sigma]
  simp only [familyBlockDisagreementCount]
  rw [Fintype.sum_sigma]
  rfl

private theorem familyBlockDisagreementCount_self
    {ι : Type*} {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) (i : ι) :
    familyBlockDisagreementCount σ τ i i = 0 := by
  classical
  unfold familyBlockDisagreementCount
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  by_cases hσ : σ.slotEquiv ⟨i, p⟩ < σ.slotEquiv ⟨i, q⟩
  · have hpq : p < q := by
      rcases lt_trichotomy p q with hpq | hpq | hpq
      · exact hpq
      · subst q
        exact absurd hσ (lt_irrefl _)
      · exact absurd (σ.strictMono i hpq) (asymm hσ)
    have hτ := τ.strictMono i hpq
    simp [hσ, asymm hτ]
  · simp [hσ]

private theorem familyBlockDisagreementCount_add_swap_mod_two
    {ι : Type*} {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total) (i j : ι) (hij : i ≠ j) :
    Nat.ModEq 2
      (familyBlockDisagreementCount σ τ i j +
        familyBlockDisagreementCount σ τ j i)
      (σ.blockInversionCount i j + τ.blockInversionCount i j) := by
  classical
  rw [σ.blockInversionCount_of_ne hij, τ.blockInversionCount_of_ne hij]
  unfold familyBlockDisagreementCount
  rw [Finset.sum_comm (f := fun q : Fin (size j) =>
    ∑ p : Fin (size i),
      if σ.slotEquiv ⟨j, q⟩ < σ.slotEquiv ⟨i, p⟩ then
        if τ.slotEquiv ⟨i, p⟩ < τ.slotEquiv ⟨j, q⟩ then 1 else 0
      else 0)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Nat.ModEq.sum ?_
  intro p hp
  refine Nat.ModEq.sum ?_
  intro q hq
  have htag : (⟨i, p⟩ : Σ k, Fin (size k)) ≠ ⟨j, q⟩ := by
    intro h
    exact hij (congrArg Sigma.fst h)
  have hσne : σ.slotEquiv ⟨i, p⟩ ≠ σ.slotEquiv ⟨j, q⟩ :=
    σ.slotEquiv.injective.ne htag
  have hτne : τ.slotEquiv ⟨i, p⟩ ≠ τ.slotEquiv ⟨j, q⟩ :=
    τ.slotEquiv.injective.ne htag
  rcases lt_or_gt_of_ne hσne with hσ | hσ <;>
    rcases lt_or_gt_of_ne hτne with hτ | hτ <;>
    simp [hσ, hτ, asymm hσ, asymm hτ, Nat.ModEq]

private theorem familyRelativePerm_inversionCount_mod_two
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total)
    (blockOrder : ι ≃ Fin (Fintype.card ι)) :
    Nat.ModEq 2
      (permInversionCount (familyRelativePerm σ τ))
      (σ.orderedBlockInversionCount blockOrder +
        τ.orderedBlockInversionCount blockOrder) := by
  classical
  rw [familyRelativePerm_inversionCount_eq_sum_blockDisagreementCount]
  let rel := familyBlockDisagreementCount σ τ
  let selected := fun i j : ι =>
    if blockOrder i < blockOrder j then
      σ.blockInversionCount i j + τ.blockInversionCount i j
    else 0
  have hfull :
      (∑ i : ι, ∑ j : ι, rel i j) =
        ∑ p ∈ (Finset.univ : Finset ι).offDiag, rel p.1 p.2 := by
    calc
      (∑ i : ι, ∑ j : ι, rel i j) =
          ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, rel p.1 p.2 := by
        rw [Finset.sum_product]
        simp
      _ = ∑ p ∈ (Finset.univ : Finset ι).offDiag, rel p.1 p.2 := by
        rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
        simp [rel, familyBlockDisagreementCount_self]
  rw [hfull]
  have hsum :=
    finset_sum_offDiag_modEq_of_pair_add_modEq
      2 (Finset.univ : Finset ι) rel selected
      (fun i _ j _ hij => by
        by_cases hlt : blockOrder i < blockOrder j
        · have hnot : ¬ blockOrder j < blockOrder i := asymm hlt
          simpa [selected, hlt, hnot, add_zero] using
            familyBlockDisagreementCount_add_swap_mod_two σ τ i j hij
        · have hgt : blockOrder j < blockOrder i := by
            have hne : blockOrder i ≠ blockOrder j := by
              intro h
              exact hij (blockOrder.injective h)
            exact lt_of_le_of_ne (le_of_not_gt hlt) hne
          have hnot : ¬ blockOrder i < blockOrder j := hlt
          simpa [selected, hnot, hgt, zero_add, add_comm] using
            familyBlockDisagreementCount_add_swap_mod_two σ τ j i hij.symm)
  have hselected :
      (∑ p ∈ (Finset.univ : Finset ι).offDiag, selected p.1 p.2) =
        σ.orderedBlockInversionCount blockOrder +
          τ.orderedBlockInversionCount blockOrder := by
    unfold FamilySlotShuffleTo.orderedBlockInversionCount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hlt : blockOrder p.1 < blockOrder p.2 <;>
      simp [selected, hlt]
  rw [hselected] at hsum
  exact hsum

private theorem familyRelativePerm_sign_eq_orderedBlockInversionCount_add
    {ι : Type*} [Fintype ι] {size : ι → ℕ} {total : ℕ}
    (σ τ : FamilySlotShuffleTo size total)
    (blockOrder : ι ≃ Fin (Fintype.card ι)) :
    Equiv.Perm.sign (familyRelativePerm σ τ) =
      (-1 : ℤˣ) ^
        (σ.orderedBlockInversionCount blockOrder +
          τ.orderedBlockInversionCount blockOrder) := by
  rw [sign_eq_neg_one_pow_permInversionCount]
  exact pow_eq_of_mod_two_eq (by decide)
    (familyRelativePerm_inversionCount_mod_two σ τ blockOrder)

variable {Mode : Type*}

/-- The relative permutation between fixed and mixed component shuffles carries exactly the fixed
external regrouping sign and the residual mixed inter-component crossing sign. -/
theorem ExternalInsertionWickDiagram.relativeComponentShuffleSign_eq_external_mul_mixedInter
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    (((Equiv.Perm.sign
      (familyRelativePerm d.componentLegShuffle
        (d.componentMixedPositionShuffle externalTime σ)) : ℤ) : ℂ)) =
      componentExternalOrderSign d blockOrder *
        (Common.Statistics.fermion.zetaInt : ℂ) ^
          d.mixedInterComponentCrossingCount externalTime σ := by
  rw [familyRelativePerm_sign_eq_orderedBlockInversionCount_add
    d.componentLegShuffle (d.componentMixedPositionShuffle externalTime σ) blockOrder]
  simp only [Int.units_pow_coe, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [pow_add]
  unfold componentExternalOrderSign
  have hfixed :=
    d.componentLegShuffle_orderedBlockInversionCount_mod_two_eq_external blockOrder
  have hmixed :=
    d.mixedInterComponentCrossingCount_mod_two_eq_orderedBlockInversionCount
      externalTime σ blockOrder
  rw [pow_eq_of_mod_two_eq (show ((-1 : ℂ) * -1) = 1 by norm_num) hfixed]
  rw [pow_eq_of_mod_two_eq (show ((-1 : ℂ) * -1) = 1 by norm_num) hmixed.symm]
  rfl

end Fermionic
end SecondQuantization
