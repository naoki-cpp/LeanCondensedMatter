import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Reindexing a sum over `Pairing (n + 1)` via `equivSigma`

A sum over larger pairings is reindexed as a double sum over the partner of position `0` and the
smaller pairing obtained by erasing that first pair.
-/

namespace Combinatorics

/-- `Fin (m + 1)`'s nonzero elements, as `Fin m`. -/
private def finSuccSubtypeEquiv (m : ℕ) :
    {j : Fin (m + 1) // (0 : Fin (m + 1)) ≠ j} ≃ Fin m where
  toFun x := x.1.pred (Ne.symm x.2)
  invFun i := ⟨i.succ, Ne.symm (Fin.succ_ne_zero i)⟩
  left_inv x := Subtype.ext (Fin.succ_pred x.1 (Ne.symm x.2))
  right_inv i := Fin.pred_succ i

private theorem Pairing.insertFirstPair_congr {n : ℕ} (Q : Pairing n)
    {j j' : Fin (2 * (n + 1))} (h : j = j') (hj : (0 : Fin (2 * (n + 1))) ≠ j)
    (hj' : (0 : Fin (2 * (n + 1))) ≠ j') : Q.insertFirstPair j hj = Q.insertFirstPair j' hj' := by
  subst h
  rfl

/-- A sum over `Pairing (n + 1)`, reindexed as a double sum over a peeled position and the smaller
pairing. -/
theorem Pairing.sum_eq_sum_sum_insertFirstPair {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Pairing (n + 1) → M) :
    ∑ pairing : Pairing (n + 1), F pairing =
      ∑ j : Fin (2 * n + 1), ∑ Q : Pairing n,
        F (Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))) := by
  rw [← Equiv.sum_comp (Pairing.equivSigma n).symm F, Fintype.sum_sigma]
  refine Fintype.sum_equiv (finSuccSubtypeEquiv (2 * n + 1))
    (fun x => ∑ Q : Pairing n, F ((Pairing.equivSigma n).symm ⟨x, Q⟩))
    (fun j => ∑ Q : Pairing n, F (Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))))
    fun x => ?_
  apply Finset.sum_congr rfl
  intro Q _
  have hx : (finSuccSubtypeEquiv (2 * n + 1) x).succ = x.1 := Fin.succ_pred x.1 (Ne.symm x.2)
  simp only [Pairing.equivSigma, Equiv.coe_fn_symm_mk]
  exact congrArg F (Q.insertFirstPair_congr hx.symm _ _)

end Combinatorics
