import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.Occupation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Algebraic bosonic Fock space

The bosonic Fock space is the free complex vector space on bosonic occupation states. It is the
algebraic, finite-support construction; no Hilbert-space completion or operator-domain theory is
included here.

The public type is `Bosonic.FockSpace`.
-/

namespace SecondQuantization
namespace Bosonic

/-- The algebraic bosonic Fock space on occupation-number states. -/
abbrev FockSpace (Mode : Type*) :=
  Common.AlgebraicFock (Occupation Mode)

variable {Mode : Type*}

/-- The basis vector corresponding to occupation state `n`. -/
noncomputable def basisState (n : Occupation Mode) : FockSpace Mode :=
  Common.basisState n

/-- The basis vector of the zero-occupation state. -/
noncomputable def fockVacuum : FockSpace Mode := basisState vacuum

end Bosonic
end SecondQuantization
