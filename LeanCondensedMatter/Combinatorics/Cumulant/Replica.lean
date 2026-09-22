import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Replica polynomials for finite-set connected expansions

A partition with `k` blocks admits an independent replica label on every block, producing the
factor `N^k`.  This file packages that block count into a polynomial in a formal replica variable
and extracts the coefficient linear in the replica count.

The construction is purely combinatorial.  In particular, it does not use partition-lattice
Möbius inversion or finite-set cumulant inversion.
-/

open scoped BigOperators

namespace Finpartition

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-- The replica-count polynomial associated with finite-set block weights.

Each partition contributes its block-product weight in degree equal to its number of blocks. -/
noncomputable def replicaPolynomial (κ : Finset α → R) (S : Finset α) : Polynomial R :=
  ∑ π : Finpartition S,
    Polynomial.C (partitionProduct κ π) * Polynomial.X ^ π.parts.card

private theorem finpartition_eq_indiscrete_of_card_parts_eq_one
    {S : Finset α} (hS : S ≠ ∅) (π : Finpartition S) (hπ : π.parts.card = 1) :
    π = indiscrete hS := by
  obtain ⟨B, hparts⟩ := Finset.card_eq_one.mp hπ
  have hBS : B = S := by
    simpa [hparts] using π.sup_parts
  subst B
  apply Finpartition.ext
  simpa using hparts

/-- For nonempty support, the coefficient linear in the replica count is exactly the one-block
contribution. -/
theorem replicaPolynomial_coeff_one (κ : Finset α → R) {S : Finset α} (hS : S ≠ ∅) :
    (replicaPolynomial κ S).coeff 1 = κ S := by
  classical
  rw [replicaPolynomial, Polynomial.finsetSum_coeff]
  change (∑ π : Finpartition S,
    (Polynomial.C (partitionProduct κ π) *
      Polynomial.X ^ π.parts.card).coeff 1) = κ S
  rw [Fintype.sum_eq_single (Finpartition.indiscrete hS) (fun π hπ => by
    have hcard : 1 ≠ π.parts.card := by
      intro h
      exact hπ (finpartition_eq_indiscrete_of_card_parts_eq_one hS π h.symm)
    simp [hcard])]
  simp [partitionProduct]


/-- Evaluating the replica polynomial at a natural replica number is the sum over independent
replica labelings of the blocks of every partition. Each labeling carries the partition's block
weight. -/
theorem replicaPolynomial_eval_nat_eq_sum_labelings
    (κ : Finset α → R) (S : Finset α) (n : ℕ) :
    (replicaPolynomial κ S).eval (n : R) =
      ∑ π : Finpartition S, ∑ _ : π.parts → Fin n, partitionProduct κ π := by
  classical
  rw [replicaPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro π hπ
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp [Fintype.card_fin, nsmul_eq_mul, mul_comm]

end Finpartition
