import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition
import LeanCondensedMatter.Combinatorics.Cumulant.Normalized

set_option linter.style.header false

/-!
# Möbius inversion for multiplicative connected decompositions

The connected-decomposition moment theorem is semiring-generic. This module adds only the reverse
Möbius-inversion statement and the normalized object-moment adapter, so consumers that need direct
object moments do not carry raw empty-set normalization plumbing.
-/

namespace Combinatorics

namespace MultiplicativeWeight

variable {α R : Type*} [DecidableEq α] [CommRing R]
variable {D : ConnectedDecomposition α} (W : MultiplicativeWeight D R)

/-- The total object moment of a multiplicative connected decomposition, bundled with its canonical
empty-set normalization. -/
noncomputable def normalizedObjectMoment : NormalizedSetFunction α R where
  toFun := W.objectMoment
  map_empty := by
    rw [W.objectMoment_eq_momentFromCumulant]
    exact Finpartition.momentFromCumulant_empty W.connectedContribution

@[simp]
theorem normalizedObjectMoment_apply (S : Finset α) :
    W.normalizedObjectMoment S = W.objectMoment S :=
  rfl

/-- The cumulant of the total object weight is the connected-object contribution. -/
theorem cumulantFromMoment_objectMoment {S : Finset α} (hS : S ≠ ∅) :
    Finpartition.cumulantFromMoment W.objectMoment S = W.connectedContribution S := by
  rw [show W.objectMoment = Finpartition.momentFromCumulant W.connectedContribution from
    funext fun T => W.objectMoment_eq_momentFromCumulant T]
  exact Finpartition.cumulantFromMoment_momentFromCumulant W.connectedContribution
    (S := S) hS

/-- On a nonempty set, the cumulant of the normalized object moment is the connected-object
contribution. -/
theorem normalizedObjectMoment_cumulant_eq_connectedContribution
    {S : Finset α} (hS : S ≠ ∅) :
    W.normalizedObjectMoment.cumulant S = W.connectedContribution S := by
  change Finpartition.cumulantFromMoment W.objectMoment S = W.connectedContribution S
  exact W.cumulantFromMoment_objectMoment hS

end MultiplicativeWeight
end Combinatorics
