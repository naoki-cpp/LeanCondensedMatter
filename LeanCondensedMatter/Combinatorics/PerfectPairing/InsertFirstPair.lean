import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero

set_option linter.style.header false

/-!
# `Pairing.insertFirstPair`, and the `Pairing (n + 1) ≃ Σ j, Pairing n` decomposition

`Pairing.insertFirstPair` inserts a new pair `(0, j)` ahead of a smaller pairing, reindexing it
onto the positions left after removing `0` and `j` — the constructive counterpart to
`PerfectPairing/EraseZero.lean`'s `Pairing.eraseZeroPair`, needed to let the finite-temperature
Bloch–de Dominicis induction build up a `Pairing (n + 1)` from a choice of `j` and a smaller
`Pairing n`, rather than only tearing one down. `eraseZeroPair_insertFirstPair`/
`insertFirstPair_eraseZeroPair` are the round-trip laws connecting the two directions, packaged
into the equivalence `Pairing.equivSigma`.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- Insert a new pair `(0, j)` ahead of a smaller pairing, reindexing it onto the positions left
after removing `0` and `j`. This is the constructive counterpart to `Pairing.eraseZeroPair` needed
to let the Bloch--de Dominicis induction build up a `Pairing (n + 1)` from a choice of `j` and a
smaller `Pairing n`, rather than only tearing one down; the round-trip laws connecting the two
directions are proved separately. -/
noncomputable def Pairing.insertFirstPair {n : ℕ} (pairing : Pairing n) (j : Fin (2 * (n + 1)))
    (hj : (0 : Fin (2 * (n + 1))) ≠ j) : Pairing (n + 1) := by
  let oi := deletedPositionsOrderIso n j hj
  let extended : Equiv.Perm (Fin (2 * (n + 1))) := pairing.partner.extendDomain oi.toEquiv
  have hext0 : extended (0 : Fin (2 * (n + 1))) = 0 :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions])
  have hextj : extended j = j :=
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions])
  have hextInv : ∀ x : Fin (2 * (n + 1)), extended (extended x) = x := by
    intro x
    by_cases hx : x ∈ deletedPositions n j hj
    · have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hx⟩)) : Fin (2 * (n + 1))) :=
        Equiv.Perm.extendDomain_apply_subtype _ _ hx
      have hx2 : extended x ∈ deletedPositions n j hj := by
        rw [h1]; exact (oi (pairing.partner (oi.symm ⟨x, hx⟩))).property
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
  have hextNe : ∀ x : Fin (2 * (n + 1)), x ∈ deletedPositions n j hj → extended x ≠ x := by
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
      · have hxmem : x ∈ deletedPositions n j hj := by simp [deletedPositions, hx0, hxj]
        have hex : extended x ∈ deletedPositions n j hj := by
          have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hxmem⟩)) : Fin (2 * (n + 1))) :=
            Equiv.Perm.extendDomain_apply_subtype _ _ hxmem
          rw [h1]; exact (oi (pairing.partner (oi.symm ⟨x, hxmem⟩))).property
        rw [Equiv.swap_apply_of_ne_of_ne
          (Finset.mem_erase.mp (Finset.mem_erase.mp hex).2).1 (Finset.mem_erase.mp hex).1,
          hextInv, Equiv.swap_apply_of_ne_of_ne hx0 hxj]
  · intro x
    rw [Equiv.Perm.mul_apply]
    by_cases hx0 : x = 0
    · subst hx0
      rw [hext0, Equiv.swap_apply_left]
      exact Ne.symm hj
    · by_cases hxj : x = j
      · subst hxj
        rw [hextj, Equiv.swap_apply_right]
        exact hj
      · have hxmem : x ∈ deletedPositions n j hj := by simp [deletedPositions, hx0, hxj]
        have hex : extended x ∈ deletedPositions n j hj := by
          have h1 : extended x = (oi (pairing.partner (oi.symm ⟨x, hxmem⟩)) : Fin (2 * (n + 1))) :=
            Equiv.Perm.extendDomain_apply_subtype _ _ hxmem
          rw [h1]; exact (oi (pairing.partner (oi.symm ⟨x, hxmem⟩))).property
        rw [Equiv.swap_apply_of_ne_of_ne
          (Finset.mem_erase.mp (Finset.mem_erase.mp hex).2).1 (Finset.mem_erase.mp hex).1]
        exact hextNe x hxmem

/-- `insertFirstPair` pairs position `0` with the chosen `j`. -/
@[simp]
theorem Pairing.insertFirstPair_partner_zero {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) :
    (pairing.insertFirstPair j hj).partner 0 = j := by
  change (Equiv.swap 0 j *
    (pairing.partner.extendDomain (deletedPositionsOrderIso n j hj).toEquiv)) 0 = j
  rw [Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions]),
    Equiv.swap_apply_left]

/-- `insertFirstPair`'s chosen partner `j` pairs back with position `0`. -/
@[simp]
theorem Pairing.insertFirstPair_partner_chosen {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) :
    (pairing.insertFirstPair j hj).partner j = 0 := by
  change (Equiv.swap 0 j *
    (pairing.partner.extendDomain (deletedPositionsOrderIso n j hj).toEquiv)) j = 0
  rw [Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp [deletedPositions]),
    Equiv.swap_apply_right]

/-- On the positions left after removing `0` and `j`, `insertFirstPair`'s partner is exactly the
smaller pairing's own partner, transported across `deletedPositionsOrderIso`: this is the
conjugation formula `eraseZeroOrderIso_partner` needs a counterpart of on the insertion side. -/
@[simp]
theorem Pairing.insertFirstPair_partner_orderIso {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) (i : Fin (2 * n)) :
    (pairing.insertFirstPair j hj).partner
        (deletedPositionsOrderIso n j hj i : Fin (2 * (n + 1))) =
      (deletedPositionsOrderIso n j hj (pairing.partner i) : Fin (2 * (n + 1))) := by
  set oi := deletedPositionsOrderIso n j hj
  change (Equiv.swap 0 j * (pairing.partner.extendDomain oi.toEquiv)) (oi i : Fin (2 * (n + 1))) =
    (oi (pairing.partner i) : Fin (2 * (n + 1)))
  rw [Equiv.Perm.mul_apply]
  have hmem : (oi i : Fin (2 * (n + 1))) ∈ deletedPositions n j hj := (oi i).property
  have h1 : pairing.partner.extendDomain oi.toEquiv (oi i : Fin (2 * (n + 1))) =
      (oi (pairing.partner (oi.symm ⟨(oi i : Fin (2 * (n + 1))), hmem⟩)) :
        Fin (2 * (n + 1))) :=
    Equiv.Perm.extendDomain_apply_subtype _ _ hmem
  rw [h1]
  have hsymm : oi.symm ⟨(oi i : Fin (2 * (n + 1))), hmem⟩ = i := by
    apply oi.injective
    simp
  rw [hsymm]
  have hmem' : (oi (pairing.partner i) : Fin (2 * (n + 1))) ∈ deletedPositions n j hj :=
    (oi (pairing.partner i)).property
  exact Equiv.swap_apply_of_ne_of_ne
    (Finset.mem_erase.mp (Finset.mem_erase.mp hmem').2).1 (Finset.mem_erase.mp hmem').1

/-- Inserting a new pair `(0, j)` ahead of `pairing`, then erasing the pair containing position
`0`, recovers `pairing` unchanged: `eraseZeroPair` is a left inverse of `insertFirstPair j hj`. -/
theorem Pairing.eraseZeroPair_insertFirstPair {n : ℕ} (pairing : Pairing n)
    (j : Fin (2 * (n + 1))) (hj : (0 : Fin (2 * (n + 1))) ≠ j) :
    (pairing.insertFirstPair j hj).eraseZeroPair = pairing := by
  set P := pairing.insertFirstPair j hj with hPdef
  have hPj : P.partner 0 = j := pairing.insertFirstPair_partner_zero j hj
  have hoi_eq : ∀ k : Fin (2 * n),
      (P.eraseZeroOrderIso k : Fin (2 * (n + 1))) =
        (deletedPositionsOrderIso n j hj k : Fin (2 * (n + 1))) :=
    deletedPositionsOrderIso_congr n hPj (Ne.symm (P.partner_ne 0)) hj
  apply Pairing.ext
  apply Equiv.ext
  intro i
  apply P.eraseZeroOrderIso.injective
  apply Subtype.ext
  rw [Pairing.eraseZeroOrderIso_partner, hoi_eq, hoi_eq]
  rw [hPdef, pairing.insertFirstPair_partner_orderIso j hj i]

/-- Erasing the pair containing position `0` from `pairing`, then reinserting a pair with the
same partner, recovers `pairing` unchanged: on the fiber of pairings with `partner 0 = j`,
`insertFirstPair j hj` is a left inverse of `eraseZeroPair`. -/
theorem Pairing.insertFirstPair_eraseZeroPair {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.eraseZeroPair.insertFirstPair (pairing.partner 0)
      (Ne.symm (pairing.partner_ne 0)) = pairing := by
  apply Pairing.ext
  apply Equiv.ext
  intro x
  by_cases hx0 : x = 0
  · subst hx0
    exact pairing.eraseZeroPair.insertFirstPair_partner_zero (pairing.partner 0)
      (Ne.symm (pairing.partner_ne 0))
  · by_cases hxj : x = pairing.partner 0
    · subst hxj
      rw [pairing.eraseZeroPair.insertFirstPair_partner_chosen (pairing.partner 0)
        (Ne.symm (pairing.partner_ne 0))]
      exact (pairing.partner_partner 0).symm
    · have hxmem : x ∈ deletedPositions n (pairing.partner 0) (Ne.symm (pairing.partner_ne 0)) := by
        simp [deletedPositions, hx0, hxj]
      set k := pairing.eraseZeroOrderIso.symm ⟨x, hxmem⟩ with hkdef
      have hxeq : (pairing.eraseZeroOrderIso k : Fin (2 * (n + 1))) = x := by simp [hkdef]
      have hkey := pairing.eraseZeroPair.insertFirstPair_partner_orderIso (pairing.partner 0)
        (Ne.symm (pairing.partner_ne 0)) k
      rw [← hxeq]
      exact hkey.trans (Pairing.eraseZeroOrderIso_partner pairing k)

/-- **A `Pairing (n + 1)` decomposes into a choice of position `0`'s partner together with the
smaller pairing left after removing it.** `eraseZeroPair_insertFirstPair` and
`insertFirstPair_eraseZeroPair` are exactly the two `Equiv.left_inv`/`right_inv` obligations this
needs: `eraseZeroPair` is not globally injective on `Pairing (n + 1)` (distinct choices of `0`'s
partner can erase to the same smaller pairing), so this is an equivalence with the fiber-indexed
sigma type, not a claim that `eraseZeroPair` alone is a global bijection. -/
noncomputable def Pairing.equivSigma (n : ℕ) :
    Pairing (n + 1) ≃ Σ _ : {j : Fin (2 * (n + 1)) // (0 : Fin (2 * (n + 1))) ≠ j}, Pairing n where
  toFun pairing := ⟨⟨pairing.partner 0, Ne.symm (pairing.partner_ne 0)⟩, pairing.eraseZeroPair⟩
  invFun jQ := jQ.2.insertFirstPair jQ.1.1 jQ.1.2
  left_inv pairing := pairing.insertFirstPair_eraseZeroPair
  right_inv jQ := by
    obtain ⟨⟨j, hj⟩, Q⟩ := jQ
    refine Sigma.ext (Subtype.ext ?_) ?_
    · exact Q.insertFirstPair_partner_zero j hj
    · exact heq_of_eq (Q.eraseZeroPair_insertFirstPair j hj)

end BlochDeDominicis
end Common
end SecondQuantization
