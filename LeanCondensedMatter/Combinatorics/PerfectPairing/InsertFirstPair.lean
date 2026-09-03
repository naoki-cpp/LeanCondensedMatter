import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import Mathlib.GroupTheory.Perm.Support

set_option linter.style.header false

/-!
# `Pairing.insertFirstPair`, and the `Pairing (n + 1) ≃ Σ j, Pairing n` decomposition

`Pairing.insertFirstPair` inserts a new pair `(0, j)` ahead of a smaller pairing, reindexing it
onto the positions left after removing `0` and `j`. The erase/insert round-trip laws package this
recursion as `Pairing.equivSigma`.
-/

namespace Combinatorics

open FiniteIndex

/-- Insert a new pair `(0, j)` ahead of a smaller pairing. -/
noncomputable def Pairing.insertFirstPair {n : ℕ} (pairing : Pairing n) (j : Fin (2 * (n + 1)))
    (hj : j ≠ (0 : Fin (2 * (n + 1)))) : Pairing (n + 1) := by
  let oi := deletedPositionsOrderIso n j hj
  let extended : Equiv.Perm (Fin (2 * (n + 1))) := pairing.partner.extendDomain oi.toEquiv
  have hext0 : extended (0 : Fin (2 * (n + 1))) = 0 :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions])
  have hextj : extended j = j :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions])
  have hpartnerSq : pairing.partner * pairing.partner = 1 := by
    apply Equiv.ext
    intro x
    simpa [Equiv.Perm.mul_apply] using pairing.partner_partner x
  have hextSq : extended * extended = 1 := by
    change pairing.partner.extendDomain oi.toEquiv * pairing.partner.extendDomain oi.toEquiv = 1
    rw [Equiv.Perm.extendDomain_mul, hpartnerSq, Equiv.Perm.extendDomain_one]
  have hextNe : ∀ x : Fin (2 * (n + 1)), x ∈ deletedPositions n j → extended x ≠ x := by
    intro x hx h
    have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hx⟩)) : Fin (2 * (n + 1))) :=
      Equiv.Perm.extendDomain_apply_subtype _ _ hx
    have h2 : oi (pairing.partner (oi.symm ⟨x, hx⟩)) = oi (oi.symm ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [← h1, h]
      simp
    have h3 : pairing.partner (oi.symm ⟨x, hx⟩) = oi.symm ⟨x, hx⟩ := oi.injective h2
    exact pairing.partner_ne _ h3
  have hdisjoint : Equiv.Perm.Disjoint (Equiv.swap 0 j) extended := by
    intro x
    by_cases hx0 : x = 0
    · right
      simpa [hx0] using hext0
    · by_cases hxj : x = j
      · right
        simpa [hxj] using hextj
      · left
        exact Equiv.swap_apply_of_ne_of_ne hx0 hxj
  have hinsertedSq :
      (Equiv.swap 0 j * extended) * (Equiv.swap 0 j * extended) = 1 := by
    calc
      (Equiv.swap 0 j * extended) * (Equiv.swap 0 j * extended) =
          Equiv.swap 0 j * (extended * Equiv.swap 0 j) * extended := by
        simp only [mul_assoc]
      _ = Equiv.swap 0 j * (Equiv.swap 0 j * extended) * extended := by
        rw [hdisjoint.commute.eq.symm]
      _ = (Equiv.swap 0 j * Equiv.swap 0 j) * (extended * extended) := by
        simp only [mul_assoc]
      _ = 1 := by
        rw [Equiv.swap_mul_self, hextSq, one_mul]
  refine Pairing.ofPartner (Equiv.swap 0 j * extended) ⟨?_, ?_⟩
  · intro x
    have hx := congrArg (fun p : Equiv.Perm (Fin (2 * (n + 1))) => p x) hinsertedSq
    simpa [Equiv.Perm.mul_apply] using hx
  · intro x hfixed
    have hboth := hdisjoint.mul_apply_eq_iff.mp hfixed
    by_cases hx0 : x = 0
    · subst x
      have hzero : j = (0 : Fin (2 * (n + 1))) := by
        simpa using hboth.1
      exact hj hzero
    · by_cases hxj : x = j
      · subst x
        have hzero : (0 : Fin (2 * (n + 1))) = j := by
          simpa using hboth.1
        exact hj hzero.symm
      · exact hextNe x (by simp [deletedPositions, hx0, hxj]) hboth.2

@[simp]
theorem Pairing.insertFirstPair_partner_zero {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) :
    (pairing.insertFirstPair j hj).partner 0 = j := by
  change (Equiv.swap 0 j *
    (pairing.partner.extendDomain (deletedPositionsOrderIso n j hj).toEquiv)) 0 = j
  rw [Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions]),
    Equiv.swap_apply_left]

@[simp]
theorem Pairing.insertFirstPair_partner_chosen {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) :
    (pairing.insertFirstPair j hj).partner j = 0 := by
  change (Equiv.swap 0 j *
    (pairing.partner.extendDomain (deletedPositionsOrderIso n j hj).toEquiv)) j = 0
  rw [Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions]),
    Equiv.swap_apply_right]

@[simp]
theorem Pairing.insertFirstPair_partner_orderIso {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) (i : Fin (2 * n)) :
    (pairing.insertFirstPair j hj).partner
        (deletedPositionsOrderIso n j hj i : Fin (2 * (n + 1))) =
      (deletedPositionsOrderIso n j hj (pairing.partner i) : Fin (2 * (n + 1))) := by
  set oi := deletedPositionsOrderIso n j hj
  change (Equiv.swap 0 j * (pairing.partner.extendDomain oi.toEquiv)) (oi i : Fin (2 * (n + 1))) =
    (oi (pairing.partner i) : Fin (2 * (n + 1)))
  rw [Equiv.Perm.mul_apply]
  have hmem : (oi i : Fin (2 * (n + 1))) ∈ deletedPositions n j := (oi i).property
  have h1 : pairing.partner.extendDomain oi.toEquiv (oi i : Fin (2 * (n + 1))) =
      (oi (pairing.partner (oi.symm ⟨(oi i : Fin (2 * (n + 1))), hmem⟩)) :
        Fin (2 * (n + 1))) :=
    Equiv.Perm.extendDomain_apply_subtype _ _ hmem
  rw [h1]
  have hsymm : oi.symm ⟨(oi i : Fin (2 * (n + 1))), hmem⟩ = i := by
    apply oi.injective
    simp
  rw [hsymm]
  have hmem' : (oi (pairing.partner i) : Fin (2 * (n + 1))) ∈ deletedPositions n j :=
    (oi (pairing.partner i)).property
  exact Equiv.swap_apply_of_ne_of_ne
    (Finset.mem_erase.mp (Finset.mem_erase.mp hmem').2).1 (Finset.mem_erase.mp hmem').1

/-- Inserting and then erasing the new first pair recovers the smaller pairing. -/
theorem Pairing.eraseZeroPair_insertFirstPair {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : j ≠ (0 : Fin (2 * (n + 1)))) :
    (pairing.insertFirstPair j hj).eraseZeroPair = pairing := by
  set P := pairing.insertFirstPair j hj with hPdef
  have hPj : P.partner 0 = j := pairing.insertFirstPair_partner_zero j hj
  have orderIso_congr {a b : Fin (2 * (n + 1))} (hab : a = b)
      (ha : a ≠ (0 : Fin (2 * (n + 1)))) (hb : b ≠ (0 : Fin (2 * (n + 1))))
      (k : Fin (2 * n)) :
      (deletedPositionsOrderIso n a ha k : Fin (2 * (n + 1))) =
        (deletedPositionsOrderIso n b hb k : Fin (2 * (n + 1))) := by
    cases hab
    rfl
  have hoi_eq : ∀ k : Fin (2 * n),
      (P.eraseZeroOrderIso k : Fin (2 * (n + 1))) =
        (deletedPositionsOrderIso n j hj k : Fin (2 * (n + 1))) := by
    intro k
    rw [Pairing.eraseZeroOrderIso]
    exact orderIso_congr hPj (P.partner_ne 0) hj k
  apply Pairing.ext
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
  apply Pairing.ext
  apply Equiv.ext
  intro x
  by_cases hx0 : x = 0
  · subst hx0
    exact pairing.eraseZeroPair.insertFirstPair_partner_zero (pairing.partner 0)
      (pairing.partner_ne 0)
  · by_cases hxj : x = pairing.partner 0
    · subst hxj
      rw [pairing.eraseZeroPair.insertFirstPair_partner_chosen (pairing.partner 0)
        (pairing.partner_ne 0)]
      exact (pairing.partner_partner 0).symm
    · have hxmem : x ∈ deletedPositions n (pairing.partner 0) := by
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

end Combinatorics
