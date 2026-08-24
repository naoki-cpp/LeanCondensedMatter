import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Occupation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Fermionic occupation Fock representation (algebraic)

The occupation-basis representation of algebraic (finite-particle, uncompleted) fermionic Fock
space is the free `ℂ`-vector space on the fermionic occupation-number basis `Occupation Mode`
(`Occupation.lean`).

Built directly on `Common.AlgebraicFock`:
`OccupationFock Mode := Common.AlgebraicFock (Occupation Mode)`, with `basisState` specializing the
generic `Common.basisState`. Generic basis extensionality is consumed directly from
`Common.linearMap_ext_basisState` rather than re-exported under a fermionic wrapper. The name
deliberately records that this representation depends on the chosen mode basis. The
basis-independent algebraic fermionic Fock construction is the exterior-algebra
`Fermionic.AlgebraicFock` and is related to this representation by a chosen-basis equivalence.
`Fermionic.CompletedFockSpace` is the separate completed `ℓ²` occupation representation.

This layer is algebraic only: no inner product, no Hilbert-space completion, and no bounded or
unbounded operator theory. Creation and annihilation operators, with their sign factors, are defined
in `CreationAnnihilation.lean`.
-/

namespace SecondQuantization
namespace Fermionic

/-- The occupation-basis representation of algebraic fermionic Fock space: the free `ℂ`-vector
space on finite occupation subsets. This is basis-dependent representation data, distinct from the
basis-independent exterior-algebra `AlgebraicFock`. -/
abbrev OccupationFock (Mode : Type*) :=
  Common.AlgebraicFock (Occupation Mode)

variable {Mode : Type*}

/-- **The basis vector** corresponding to occupation-number state `n`. -/
noncomputable def basisState (n : Occupation Mode) : OccupationFock Mode :=
  Common.basisState n

/-- **The occupation-basis Fock vacuum vector**, the basis vector of the empty occupation state. -/
noncomputable def fockVacuum : OccupationFock Mode := basisState vacuum

end Fermionic
end SecondQuantization
