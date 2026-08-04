import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.Occupation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

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

variable {Mode : Type*} [DecidableEq Mode]

/-- The algebraic bosonic Fock space on occupation-number states. -/
abbrev FockSpace (Mode : Type*) := Common.AlgebraicFock (Occupation Mode)

/-- The basis vector corresponding to occupation state `n`. -/
noncomputable def basisState (n : Occupation Mode) : FockSpace Mode :=
  Common.basisState n

/-- The basis vector of the zero-occupation state. -/
noncomputable def fockVacuum : FockSpace Mode := basisState vacuum

@[simp]
theorem basisState_ne_zero (n : Occupation Mode) : basisState n ≠ 0 :=
  Common.basisState_ne_zero n

theorem basisState_injective : Function.Injective (basisState : Occupation Mode → _) :=
  Common.basisState_injective

/-- Basis vectors are injective on all occupation states. -/
theorem basisState_injOn : Set.InjOn (basisState : Occupation Mode → _) Set.univ :=
  fun _ _ _ _ h => basisState_injective h

/-- The occupation-number basis vectors are linearly independent. -/
theorem basisState_linearIndependent :
    LinearIndependent ℂ (basisState : Occupation Mode → FockSpace Mode) := by
  change LinearIndependent ℂ (fun n => Finsupp.single n (1 : ℂ))
  exact Finsupp.basisSingleOne.linearIndependent

/-- Linear maps out of `FockSpace Mode` are determined by their values on basis states. -/
theorem linearMap_ext_basisState {f g : FockSpace Mode →ₗ[ℂ] FockSpace Mode}
    (h : ∀ n, f (basisState n) = g (basisState n)) : f = g :=
  Common.linearMap_ext_basisState h

end Bosonic
end SecondQuantization
