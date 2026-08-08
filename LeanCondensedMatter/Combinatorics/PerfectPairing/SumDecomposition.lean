import LeanCondensedMatter.Combinatorics.PerfectPairing
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# Reindexing a sum over `Pairing (n + 1)` via `equivSigma`

A sum over larger pairings is reindexed as a double sum over the partner of position `0` and the
smaller pairing obtained by erasing that first pair.
-/

namespace Combinatorics

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
  let eNe :
      {j : Fin (2 * (n + 1)) // (0 : Fin (2 * (n + 1))) ≠ j} ≃
        {j : Fin (2 * (n + 1)) // j ≠ 0} :=
    Equiv.subtypeEquivRight (fun _ => ne_comm)
  let e :
      {j : Fin (2 * (n + 1)) // (0 : Fin (2 * (n + 1))) ≠ j} ≃ Fin (2 * n + 1) :=
    eNe.trans (finSuccAboveEquiv (0 : Fin (2 * n + 2))).symm
  refine Fintype.sum_equiv e
    (fun x => ∑ Q : Pairing n, F ((Pairing.equivSigma n).symm ⟨x, Q⟩))
    (fun j => ∑ Q : Pairing n, F (Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))))
    fun x => ?_
  apply Finset.sum_congr rfl
  intro Q _
  have hxSubtype :=
    (finSuccAboveEquiv (0 : Fin (2 * n + 2))).apply_symm_apply (eNe x)
  have hx : (e x).succ = x.1 := by
    change ((finSuccAboveEquiv (0 : Fin (2 * n + 2))).symm (eNe x)).succ = x.1
    have hxVal := congrArg Subtype.val hxSubtype
    rw [finSuccAboveEquiv_apply] at hxVal
    simpa using hxVal
  simp only [Pairing.equivSigma, Equiv.coe_fn_symm_mk]
  exact congrArg F (Q.insertFirstPair_congr hx.symm _ _)

end Combinatorics
