import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Occupation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Fermionic Fock space (algebraic)

Phase 3 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
algebraic (finite-particle, uncompleted) fermionic Fock space — the free `ℂ`-vector space on the
fermionic occupation-number basis `Occupation Mode` (`Occupation.lean`).

Built directly on `Common.AlgebraicFock`: `FockSpace Mode := Common.AlgebraicFock
(Occupation Mode)`, with `basisState`/`linearMap_ext_basisState` reusing the generic
`Common` versions rather than re-proving them. Deliberately algebraic only: no inner product, no
Hilbert-space completion, no bounded/unbounded operator theory. Those analytic questions are out of
scope until the algebraic Linked Cluster Theorem is done (see
`notes/roadmaps/second-quantization.md`'s design principles). Creation and annihilation operators,
with their sign factors, come next (`CreationAnnihilation.lean`).
-/

namespace SecondQuantization
namespace Fermionic

/-- **The algebraic fermionic Fock space.** The free `ℂ`-vector space on the basis
`Occupation Mode` — finite `ℂ`-linear combinations of occupation-number states, reusing
`Common.AlgebraicFock`. -/
abbrev FockSpace (Mode : Type*) :=
  Common.AlgebraicFock (Occupation Mode)

variable {Mode : Type*}

/-- **The basis vector** corresponding to occupation-number state `n`. -/
noncomputable def basisState (n : Occupation Mode) : FockSpace Mode :=
  Common.basisState n

/-- **The Fock vacuum vector**, the basis vector of the empty occupation state. -/
noncomputable def fockVacuum : FockSpace Mode := basisState vacuum

@[simp]
theorem basisState_ne_zero (n : Occupation Mode) : basisState n ≠ 0 :=
  Common.basisState_ne_zero n

theorem basisState_injective : Function.Injective (basisState : Occupation Mode → _) :=
  Common.basisState_injective

/-- Basis vectors are injective on all fermionic occupation states. -/
theorem basisState_injOn : Set.InjOn (basisState : Occupation Mode → _) Set.univ := by
  simpa [basisState] using
    (Common.basisState_injOn (Config := Occupation Mode))

/-- The fermionic occupation-number basis vectors are linearly independent. -/
theorem basisState_linearIndependent :
    LinearIndependent ℂ (basisState : Occupation Mode → FockSpace Mode) := by
  simpa [basisState] using
    (Common.basisState_linearIndependent (Config := Occupation Mode))

/-- Two linear maps out of `FockSpace Mode` that agree on every basis state are equal —
the basis-level facts proved in `CreationAnnihilation.lean`/`CanonicalAnticommutationRelations.lean`
suffice to establish the operator identities. -/
theorem linearMap_ext_basisState {f g : FockSpace Mode →ₗ[ℂ] FockSpace Mode}
    (h : ∀ n, f (basisState n) = g (basisState n)) : f = g :=
  Common.linearMap_ext_basisState h

end Fermionic
end SecondQuantization
