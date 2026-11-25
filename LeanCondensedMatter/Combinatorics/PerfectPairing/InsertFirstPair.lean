import LeanCondensedMatter.Combinatorics.FiniteIndex.DeletedPositions
import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# `Pairing.insertFirstPair`, and the `Pairing (n + 1) ≃ Σ j, Pairing n` decomposition

`Pairing.insertFirstPair` inserts a new pair `(0, j)` ahead of a smaller pairing, reindexing it
onto the positions left after removing `0` and `j`. The erase/insert round-trip laws package this
recursion as `Pairing.equivSigma`. The same module provides the general product and sum
factorizations along that equivalence.
-/

namespace Combinatorics

open FiniteIndex

/-- The pairing on a two-element type. -/
private def boolPairing : PairingOn Bool :=
  PairingOn.ofPartner (Equiv.swap false true) (by decide)

/-- Insert a new pair `(0, j)` ahead of a smaller pairing. -/
noncomputable def Pairing.insertFirstPair {n : ℕ} (pairing : Pairing n) (j : Fin (2 * (n + 1)))
    (hj : j ≠ (0 : Fin (2 * (n + 1)))) : Pairing (n + 1) :=
  (boolPairing.sumCongr pairing).transport (deletedPositionsSumEquiv (2 * n) j hj).symm

@[simp]
theorem Pairing.insertFirstPair_partner_zero {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) :
    (pairing.insertFirstPair j hj).partner 0 = j := by
  let e := deletedPositionsSumEquiv (2 * n) j hj
  change (pairing.insertFirstPair j hj).partner (e (Sum.inl false)) = e (Sum.inl true)
  change ((boolPairing.sumCongr pairing).transport e.symm).partner
    (e (Sum.inl false)) = e (Sum.inl true)
  rw [PairingOn.transport_partner, Equiv.symm_apply_apply, PairingOn.sumCongr_partner_inl]
  rfl

private theorem Pairing.insertFirstPair_partner_orderIso {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) (i : Fin (2 * n)) :
    (pairing.insertFirstPair j hj).partner
        (deletedPositionsOrderIso (2 * n) j hj i : Fin (2 * (n + 1))) =
      (deletedPositionsOrderIso (2 * n) j hj (pairing.partner i) : Fin (2 * (n + 1))) := by
  let e := deletedPositionsSumEquiv (2 * n) j hj
  change ((boolPairing.sumCongr pairing).transport e.symm).partner
    (e (Sum.inr i)) = e (Sum.inr (pairing.partner i))
  rw [PairingOn.transport_partner, Equiv.symm_apply_apply, PairingOn.sumCongr_partner_inr]
  rfl

/-- Inserting and then erasing the new first pair recovers the smaller pairing. -/
theorem Pairing.eraseZeroPair_insertFirstPair {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) :
    (pairing.insertFirstPair j hj).eraseZeroPair = pairing := by
  set P := pairing.insertFirstPair j hj with hPdef
  have hPj : P.partner 0 = j := pairing.insertFirstPair_partner_zero j hj
  have orderIso_congr {a b : Fin (2 * (n + 1))} (hab : a = b)
      (ha : a ≠ (0 : Fin (2 * (n + 1)))) (hb : b ≠ (0 : Fin (2 * (n + 1))))
      (k : Fin (2 * n)) :
      (deletedPositionsOrderIso (2 * n) a ha k : Fin (2 * (n + 1))) =
        (deletedPositionsOrderIso (2 * n) b hb k : Fin (2 * (n + 1))) := by
    cases hab
    rfl
  have hoi_eq : ∀ k : Fin (2 * n),
      (P.eraseZeroOrderIso k : Fin (2 * (n + 1))) =
        (deletedPositionsOrderIso (2 * n) j hj k : Fin (2 * (n + 1))) := by
    intro k
    rw [Pairing.eraseZeroOrderIso]
    exact orderIso_congr hPj (P.partner_ne 0) hj k
  apply PairingOn.ext
  apply Equiv.ext
  intro i
  apply P.eraseZeroOrderIso.injective
  apply Subtype.ext
  rw [Pairing.eraseZeroOrderIso_partner, hoi_eq, hoi_eq]
  rw [hPdef, pairing.insertFirstPair_partner_orderIso j hj i]

/-- Erasing and reinserting the first pair recovers the original pairing. -/
theorem Pairing.insertFirstPair_eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.eraseZeroPair.insertFirstPair (pairing.partner 0)
      (pairing.partner_ne 0) = pairing := by
  apply PairingOn.ext
  apply Equiv.ext
  intro x
  by_cases hx0 : x = 0
  · subst hx0
    exact pairing.eraseZeroPair.insertFirstPair_partner_zero (pairing.partner 0)
      (pairing.partner_ne 0)
  · by_cases hxj : x = pairing.partner 0
    · subst hxj
      have hpartner :=
        (pairing.eraseZeroPair.insertFirstPair (pairing.partner 0)
          (pairing.partner_ne 0)).partner_partner 0
      rw [pairing.eraseZeroPair.insertFirstPair_partner_zero (pairing.partner 0)
        (pairing.partner_ne 0)] at hpartner
      exact hpartner.trans (pairing.partner_partner 0).symm
    · have hxmem : x ∈ deletedPositions (2 * n) (pairing.partner 0) := by
        simp [deletedPositions, hx0, hxj]
      set k := pairing.eraseZeroOrderIso.symm ⟨x, hxmem⟩ with hkdef
      have hxeq : (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1))) = x := by simp [hkdef]
      have hkey := pairing.eraseZeroPair.insertFirstPair_partner_orderIso (pairing.partner 0)
        (pairing.partner_ne 0) k
      rw [← hxeq]
      exact hkey.trans (Pairing.eraseZeroOrderIso_partner pairing k)

/-- A pairing decomposes into the partner of `0` and the smaller pairing obtained by erasing it. -/
noncomputable def Pairing.equivSigma (n : ℕ) :
    Pairing (n + 1) ≃ Σ _ : {j : Fin (2 * (n + 1)) // j ≠ (0 : Fin (2 * (n + 1)))}, Pairing n where
  toFun pairing := ⟨⟨pairing.partner 0, pairing.partner_ne 0⟩, pairing.eraseZeroPair⟩
  invFun jQ := jQ.2.insertFirstPair jQ.1.1 jQ.1.2
  left_inv pairing := pairing.insertFirstPair_eraseZeroPair
  right_inv jQ := by
    obtain ⟨⟨j, hj⟩, Q⟩ := jQ
    refine Sigma.ext (Subtype.ext ?_) ?_
    · exact Q.insertFirstPair_partner_zero j hj
    · exact heq_of_eq (Q.eraseZeroPair_insertFirstPair j hj)


/-- A product over `pairing.pairs` splits into the `firstPair` factor times a product over the
smaller pairing's own pairs. -/
theorem Pairing.prod_pairs_eq_firstPair_mul {n : ℕ} {M : Type*} [CommMonoid M]
    (pairing : Pairing (n + 1)) (f : Fin (2 * (n + 1)) × Fin (2 * (n + 1)) → M) :
    ∏ pr ∈ pairing.pairs, f pr =
      f pairing.firstPair *
        ∏ pr ∈ pairing.eraseZeroPair.pairs,
          f ((pairing.eraseZeroOrderIso pr.1 : Fin (2 * (n + 1))),
            (pairing.eraseZeroOrderIso pr.2 : Fin (2 * (n + 1)))) := by
  classical
  rw [← Finset.insert_erase pairing.firstPair_mem_pairs,
    pairing.pairs_erase_firstPair_eq_image]
  rw [Finset.prod_insert, Finset.prod_image]
  · rfl
  · intro p _ q _ h
    exact pairing.eraseZeroPairEmbedding.injective h
  · rw [← pairing.pairs_erase_firstPair_eq_image]
    simp

/-- A sum over `Pairing (n + 1)`, reindexed as a double sum over a peeled position and the smaller
pairing. -/
theorem Pairing.sum_eq_sum_sum_insertFirstPair {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Pairing (n + 1) → M) :
    ∑ pairing : Pairing (n + 1), F pairing =
      ∑ j : Fin (2 * n + 1), ∑ Q : Pairing n,
        F (Q.insertFirstPair j.succ (Fin.succ_ne_zero j)) := by
  rw [← Equiv.sum_comp (Pairing.equivSigma n).symm F, Fintype.sum_sigma]
  let e :
      {j : Fin (2 * (n + 1)) // j ≠ 0} ≃ Fin (2 * n + 1) :=
    (finSuccAboveEquiv (0 : Fin (2 * n + 2))).symm
  refine Fintype.sum_equiv e
    (fun x => ∑ Q : Pairing n, F ((Pairing.equivSigma n).symm ⟨x, Q⟩))
    (fun j => ∑ Q : Pairing n, F (Q.insertFirstPair j.succ (Fin.succ_ne_zero j)))
    fun x => ?_
  apply Finset.sum_congr rfl
  intro Q _
  have hxSubtype :=
    (finSuccAboveEquiv (0 : Fin (2 * n + 2))).apply_symm_apply x
  have hx : (e x).succ = x.1 := by
    change ((finSuccAboveEquiv (0 : Fin (2 * n + 2))).symm x).succ = x.1
    have hxVal := congrArg Subtype.val hxSubtype
    rw [finSuccAboveEquiv_apply] at hxVal
    simpa using hxVal
  simp only [Pairing.equivSigma, Equiv.coe_fn_symm_mk, hx]

end Combinatorics
