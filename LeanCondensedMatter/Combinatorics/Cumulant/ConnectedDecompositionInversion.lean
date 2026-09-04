import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.Combinatorics.Cumulant.Inversion

set_option linter.style.header false

/-!
# Möbius inversion for multiplicative connected decompositions

The connected-decomposition moment theorem is semiring-generic. This module adds only the reverse
Möbius-inversion statement, so consumers that need direct object moments do not inherit the
partition-lattice inversion dependency.
-/

namespace Combinatorics

namespace MultiplicativeWeight

variable {α R : Type*} [DecidableEq α] [CommRing R]
variable {D : ConnectedDecomposition α} (W : MultiplicativeWeight D R)

/-- The cumulant of the total object weight is the connected-object contribution. -/
theorem cumulantFromMoment_objectMoment {S : Finset α} (hS : S ≠ ∅) :
    Finpartition.cumulantFromMoment W.objectMoment S = W.connectedContribution S := by
  rw [show W.objectMoment = Finpartition.momentFromCumulant W.connectedContribution from
    funext fun T => W.objectMoment_eq_momentFromCumulant T]
  exact Finpartition.cumulantFromMoment_momentFromCumulant W.connectedContribution
    (S := S) hS

end MultiplicativeWeight
end Combinatorics
