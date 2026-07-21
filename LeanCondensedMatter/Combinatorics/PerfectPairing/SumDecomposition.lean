import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Reindexing a sum over `Pairing (n + 1)` via `equivSigma`

`PerfectPairing.lean`'s `Pairing.equivSigma` decomposes `Pairing (n + 1)` as a choice of `0`'s
partner `j` together with the smaller pairing left after removing it. This file turns that `Equiv`
into a `Finset.sum` reindexing identity: a sum over `Pairing (n + 1)` equals a double sum, first
over positions `j : Fin (2 * n + 1)` (matching `PeelTermsIndexed.lean`'s peeled-term indexing),
then over the smaller `Pairing n`, reassembled via `Pairing.insertFirstPair` — the form
`Common/BlochDeDominicis/Induction.lean`'s general theorem needs to reassemble a `Pairing n` sum
from a peeled-position sum.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- **`Fin (m + 1)`'s nonzero elements, as `Fin m`** — the increasing bijection `j ↦ j.pred`,
inverse `i ↦ i.succ`. -/
private def finSuccSubtypeEquiv (m : ℕ) :
    {j : Fin (m + 1) // (0 : Fin (m + 1)) ≠ j} ≃ Fin m where
  toFun x := x.1.pred (Ne.symm x.2)
  invFun i := ⟨i.succ, Ne.symm (Fin.succ_ne_zero i)⟩
  left_inv x := Subtype.ext (Fin.succ_pred x.1 (Ne.symm x.2))
  right_inv i := Fin.pred_succ i

/-- **`insertFirstPair` only depends on the *value* of `j`, not on which proof of `0 ≠ j` is
supplied** — proof irrelevance makes this `rfl` once the values are identified by `subst`, but
stating it separately avoids the dependent-rewrite issues that arise from rewriting `j` directly
inside a goal already mentioning `insertFirstPair j hj`. -/
private theorem Pairing.insertFirstPair_congr {n : ℕ} (Q : Pairing n)
    {j j' : Fin (2 * (n + 1))} (h : j = j') (hj : (0 : Fin (2 * (n + 1))) ≠ j)
    (hj' : (0 : Fin (2 * (n + 1))) ≠ j') : Q.insertFirstPair j hj = Q.insertFirstPair j' hj' := by
  subst h
  rfl

/-- **A sum over `Pairing (n + 1)`, reindexed as a double sum over a peeled position and the
smaller pairing.** -/
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

end BlochDeDominicis
end Common
end SecondQuantization
