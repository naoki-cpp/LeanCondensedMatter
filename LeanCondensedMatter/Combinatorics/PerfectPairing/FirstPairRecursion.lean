import LeanCondensedMatter.Combinatorics.PerfectPairing.EraseZeroSuccAbove
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairsDecomposition
import LeanCondensedMatter.Combinatorics.PerfectPairing.SumDecomposition
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingEraseZero
import LeanCondensedMatter.Combinatorics.PerfectPairing.InsertFirstPair

set_option linter.style.header false

/-!
# The Wick/Bloch–de Dominicis pairing recursion, abstracted away from `gibbsExpectation`

`Common/BlochDeDominicis/Induction.lean`'s general theorem interleaves two independent kinds of
reasoning: analytic facts about Gibbs expectations (`gibbsExpectation_peel_indexed`, the two-point
identity, list reindexing) and purely combinatorial bookkeeping about `Pairing` (the
`equivSigma`/`insertFirstPair` double-sum reindexing, `crossingCount`'s erase-zero recursion, and
`pairs`' erase-zero product decomposition). This file isolates the combinatorial half as a
standalone theorem, `moment_eq_pairing_sum_of_first_pair_recursion`, with no dependence on
`Statistics`, `ℂ`, `AlgebraicFock`, or any KMS/evolution machinery — only a commutative semiring
`R` and an involutive scalar `ζ : R` (`ζ * ζ = 1`), general enough to cover both bosonic and
fermionic exchange statistics while staying recognizable as *this* recursion rather than an
arbitrary matching framework.

The recursion does **not** hold for an arbitrary family `C : Fin (2 * n) → α`: the concrete
Gibbs-expectation instance needs `C`'s entries to be eigenoperators of the free evolution, have
scalar commutators, and avoid resonance, and the induction step must carry those hypotheses down to
each `succAbove`-erased subfamily. The abstract theorem accordingly takes an explicit `Admissible`
predicate, closed under the same erasure `fun i => C ((j.succAbove i).succ)` already used
throughout `EraseZeroSuccAbove.lean`/`InsertFirstPair.lean`, rather than assuming the recursion
holds unconditionally.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- A power of an involutive scalar (`ζ * ζ = 1`) only depends on the exponent's parity. -/
theorem pow_eq_of_mod_two_eq {R : Type*} [CommSemiring R] {ζ : R} (hζ : ζ * ζ = 1) {a b : ℕ}
    (h : a % 2 = b % 2) : ζ ^ a = ζ ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 2]
  conv_rhs => rw [← Nat.div_add_mod b 2, ← h]
  rw [pow_add, pow_add, pow_mul, pow_mul, sq, hζ, one_pow, one_pow]

/-- **The abstract Wick/Bloch–de Dominicis pairing recursion.** Given a `moment` function
satisfying the base case `moment 0 _ = 1` and, on `Admissible` families, the first-pair recursion
`moment (n+1) C = ∑ j, ζ ^ j * pairValue (C 0) (C j.succ) * moment n (erase j C)` — with
`Admissible` closed under that same erasure — `moment n C` equals the `Pairing n`-weighted sum of
products of `pairValue`, matching `∑ pairing, ζ ^ pairing.crossingCount * ∏ pr ∈ pairing.pairs,
pairValue (C pr.1) (C pr.2)`. -/
theorem moment_eq_pairing_sum_of_first_pair_recursion {α R : Type*} [CommSemiring R] (ζ : R)
    (hζ : ζ * ζ = 1) (moment : (n : ℕ) → (Fin (2 * n) → α) → R) (pairValue : α → α → R)
    (Admissible : (n : ℕ) → (Fin (2 * n) → α) → Prop)
    (moment_zero : ∀ C : Fin 0 → α, moment 0 C = 1)
    (admissible_erase : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → α), Admissible (n + 1) C →
      ∀ j : Fin (2 * n + 1),
        Admissible n (fun i : Fin (2 * n) => C ((j.succAbove i).succ)))
    (moment_succ : ∀ (n : ℕ) (C : Fin (2 * (n + 1)) → α), Admissible (n + 1) C →
      moment (n + 1) C =
        ∑ j : Fin (2 * n + 1), ζ ^ (j : ℕ) * pairValue (C 0) (C j.succ) *
          moment n (fun i : Fin (2 * n) => C ((j.succAbove i).succ))) :
    ∀ (n : ℕ) (C : Fin (2 * n) → α), Admissible n C →
      moment n C =
        ∑ P : Pairing n, ζ ^ P.crossingCount * ∏ pr ∈ P.pairs, pairValue (C pr.1) (C pr.2) := by
  intro n
  induction n with
  | zero =>
    intro C _
    have p0 : Pairing 0 :=
      Pairing.ofPartner (Equiv.refl (Fin 0)) ⟨fun i => i.elim0, fun i => i.elim0⟩
    have hUniq : ∀ pairing : Pairing 0, pairing = p0 := fun pairing =>
      Pairing.ext (Equiv.ext fun i => i.elim0)
    have hpairs0 : p0.pairs = (∅ : Finset (Fin 0 × Fin 0)) := by simp [Pairing.pairs]
    have hcc0 : p0.crossingCount = 0 := by simp [Pairing.crossingCount, hpairs0]
    rw [moment_zero, Fintype.sum_eq_single p0 (fun pairing hne => absurd (hUniq pairing) hne)]
    simp [hpairs0, hcc0]
  | succ m ih =>
    intro C hAdm
    rw [moment_succ m C hAdm]
    rw [Pairing.sum_eq_sum_sum_insertFirstPair
      (fun pairing : Pairing (m + 1) => ζ ^ pairing.crossingCount *
        ∏ pr ∈ pairing.pairs, pairValue (C pr.1) (C pr.2))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hIH := ih (fun i : Fin (2 * m) => C ((j.succAbove i).succ)) (admissible_erase m C hAdm j)
    rw [hIH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Q _ => ?_
    set P := Q.insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j)) with hP
    have hPe : P.eraseZeroPair = Q :=
      Q.eraseZeroPair_insertFirstPair j.succ (Ne.symm (Fin.succ_ne_zero j))
    have hP0 : P.partner 0 = j.succ :=
      Q.insertFirstPair_partner_zero j.succ (Ne.symm (Fin.succ_ne_zero j))
    have hweight : ζ ^ P.crossingCount = ζ ^ (j : ℕ) * ζ ^ Q.crossingCount := by
      rw [P.crossingCount_eraseZeroPair, pow_add, hPe, mul_comm]
      congr 1
      rw [pow_eq_of_mod_two_eq hζ P.crossingsWithFirstPair_mod_two]
      congr 1
      rw [Pairing.interveningPositionCount, hP0]
      simp
    have hpred : (P.partner 0).pred (P.partner_ne 0) = j := by
      apply Fin.succ_injective
      rw [Fin.succ_pred, hP0]
    have heraseiso : ∀ pr : Fin (2 * m), (P.eraseZeroOrderIso pr : Fin (2 * (m + 1))) =
        (j.succAbove pr).succ := by
      intro pr
      rw [P.eraseZeroOrderIso_eq_succ_succAbove, hpred]
    have hprod : ∏ pr ∈ P.pairs, pairValue (C pr.1) (C pr.2) =
        pairValue (C 0) (C j.succ) *
          ∏ pr ∈ Q.pairs, pairValue (C (j.succAbove pr.1).succ) (C (j.succAbove pr.2).succ) := by
      rw [P.prod_pairs_eq_firstPair_mul]
      congr 1
      · rw [Pairing.firstPair, hP0]
      · rw [hPe]
        refine Finset.prod_congr rfl fun pr _ => ?_
        rw [heraseiso pr.1, heraseiso pr.2]
    rw [hweight, hprod]
    ring

end BlochDeDominicis
end Common
end SecondQuantization
