import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero

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
  have hextInv : ∀ x : Fin (2 * (n + 1)), extended (extended x) = x := by
    intro x
    by_cases hx : x ∈ deletedPositions n j
    · have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hx⟩)) : Fin (2 * (n + 1))) :=
        Equiv.Perm.extendDomain_apply_subtype _ _ hx
      have hx2 : extended x ∈ deletedPositions n j := by
        rw [h1]
        exact (oi (pairing.partner (oi.symm ⟨x, hx⟩))).property
      have h2 : extended (extended x) =
          (oi (pairing.partner (oi.symm ⟨extended x, hx2⟩)) : Fin (2 * (n + 1))) :=
        Equiv.Perm.extendDomain_apply_subtype _ _ hx2
      rw [h2]
      have hsymm : oi.symm ⟨extended x, hx2⟩ = pairing.partner (oi.symm ⟨x, hx⟩) := by
        apply oi.injective
        simp [h1]
      rw [hsymm, pairing.partner_partner]
      simp
    · have hx' : extended x = x := Equiv.Perm.extendDomain_apply_not_subtype _ _ hx
      rw [hx', hx']
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
  refine Pairing.ofPartner (Equiv.swap 0 j * extended) ⟨?_, ?_⟩
  · intro x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hx0 : x = 0
    · subst hx0
      rw [hext0, Equiv.swap_apply_left, hextj, Equiv.swap_apply_right]
    · by_cases hxj : x = j
      · subst hxj
        rw [hextj, Equiv.swap_apply_right, hext0, Equiv.swap_apply_left]
      · have hxmem : x ∈ deletedPositions n j := by simp [deletedPositions, hx0, hxj]
        have hex : extended x ∈ deletedPositions n j := by
          have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hxmem⟩)) : Fin (2 * (n + 1))) :=
            Equiv.Perm.extendDomain_apply_subtype _ _ hxmem
          rw [h1]
          exact (oi (pairing.partner (oi.symm ⟨x, hxmem⟩))).property
        rw [Equiv.swap_apply_of_ne_of_ne
          (Finset.mem_erase.mp (Finset.mem_erase.mp hex).2).1 (Finset.mem_erase.mp hex).1,
          hextInv, Equiv.swap_apply_of_ne_of_ne hx0 hxj]
  · intro x
    rw [Equiv.Perm.mul_apply]
    by_cases hx0 : x = 0
    · subst hx0
      rw [hext0, Equiv.swap_apply_left]
      exact hj
    · by_cases hxj : x = j
      · subst hxj
        rw [hextj, Equiv.swap_apply_right]
        exact Ne.symm hj
      · have hxmem : x ∈ deletedPositions n j := by simp [deletedPositions, hx0, hxj]
        have hex : extended x ∈ deletedPositions n j := by
          have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hxmem⟩)) : Fin (2 * (n + 1))) :=
            Equiv.Perm.extendDomain_apply_subtype _ _ hxmem
          rw [h1]
          exact (oi (pairing.partner (oi.symm ⟨x, hxmem⟩))).property
        rw [Equiv.swap_apply_of_ne_of_ne
          (Finset.mem_erase.mp (Finset.mem_erase.mp hex).2).1 (Finset.mem_erase.mp hex).1]
        exact hextNe x hxmem

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
