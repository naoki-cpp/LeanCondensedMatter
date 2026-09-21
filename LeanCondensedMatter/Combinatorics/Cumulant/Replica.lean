import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import Mathlib.Algebra.Polynomial.Coeff
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

namespace Combinatorics

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-- The replica-count polynomial associated with finite-set block weights.

Each partition contributes its block-product weight in degree equal to its number of blocks. -/
noncomputable def replicaPolynomial (κ : Finset α → R) (S : Finset α) : Polynomial R :=
  ∑ π : Finpartition S,
    Polynomial.C (Finpartition.partitionProduct κ π) * Polynomial.X ^ π.parts.card

private theorem finpartition_eq_indiscrete_of_card_parts_eq_one
    {S : Finset α} (hS : S ≠ ∅) (π : Finpartition S) (hπ : π.parts.card = 1) :
    π = Finpartition.indiscrete hS := by
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
    (Polynomial.C (Finpartition.partitionProduct κ π) *
      Polynomial.X ^ π.parts.card).coeff 1) = κ S
  rw [Fintype.sum_eq_single (Finpartition.indiscrete hS) (fun π hπ => by
    have hcard : π.parts.card ≠ 1 := by
      intro h
      exact hπ (finpartition_eq_indiscrete_of_card_parts_eq_one hS π h)
    simp [hcard])]
  simp [Finpartition.partitionProduct]

/-- The number of ways to assign one of `n` replica labels independently to every block of a
partition is `n` raised to the number of blocks. -/
theorem card_replicaLabelings {S : Finset α} (π : Finpartition S) (n : ℕ) :
    Fintype.card (π.parts → Fin n) = n ^ π.parts.card := by
  rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

end Combinatorics
