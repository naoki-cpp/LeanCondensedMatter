import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false

/-!
# Finite-index congruence

Small reindexing lemmas for replacing `Fin m` by `Fin n` when their cardinalities are
propositionally equal.
-/

namespace Combinatorics
namespace FiniteIndex

/-- Reindex a finite sum along an equality of `Fin` cardinalities. -/
theorem sum_cast {M : Type*} [AddCommMonoid M] {m n : ℕ} (h : m = n) (f : Fin m → M) :
    (∑ i : Fin m, f i) = ∑ j : Fin n, f (Fin.cast h.symm j) := by
  subst n
  rfl

end FiniteIndex
end Combinatorics
