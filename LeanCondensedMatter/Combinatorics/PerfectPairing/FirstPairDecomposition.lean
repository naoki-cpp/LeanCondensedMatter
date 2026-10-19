import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.InsertFirstPair
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# First-pair decompositions of perfect pairings

Product factorization along the first pair uses the structural residual-pair decomposition.
Sum reindexing uses the equivalence between a larger pairing and its first partner together
with the remaining smaller pairing. Neither result depends on crossing geometry.
-/

namespace Combinatorics

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
