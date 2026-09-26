import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Occupation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Fermionic occupation Fock representation (algebraic)

The occupation-basis representation of algebraic, uncompleted fermionic Fock space is the free
`ℂ`-vector space on fermionic occupation states `Occupation Mode`.

`OccupationFock Mode` is `Common.AlgebraicFock (Occupation Mode)`, and its basis states specialize
the generic `Common.basisState`. Basis extensionality and the other representation-independent
linear-algebra facts are supplied by the common algebraic Fock API. This representation depends on a
chosen mode basis; the basis-independent algebraic fermionic Fock construction is the exterior
algebra `Fermionic.AlgebraicFock`, related to it by a chosen-basis equivalence.
`Fermionic.CompletedFockSpace` is the corresponding completed `ℓ²` occupation representation.

This layer is algebraic only: it introduces no inner product, Hilbert-space completion, or bounded or
unbounded operator theory.
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
