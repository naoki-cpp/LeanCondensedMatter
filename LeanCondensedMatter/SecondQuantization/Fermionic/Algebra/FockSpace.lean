import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Occupation
import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# Fermionic occupation Fock representation (algebraic)

Phase 3 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
occupation-basis representation of algebraic (finite-particle, uncompleted) fermionic Fock space —
the free `ℂ`-vector space on the fermionic occupation-number basis `Occupation Mode`
(`Occupation.lean`).

Built directly on `Common.AlgebraicFock`:
`OccupationFock Mode := Common.AlgebraicFock (Occupation Mode)`, with
`basisState`/`linearMap_ext_basisState` reusing the generic `Common` versions rather than
re-proving them. The name deliberately records that this representation depends on the chosen mode
basis. The basis-independent algebraic fermionic Fock construction is the exterior-algebra
`Fermionic.AlgebraicFock` and is related to this representation by a chosen-basis equivalence.

This layer is algebraic only: no inner product, no Hilbert-space completion, no bounded/unbounded
operator theory. Those analytic questions are out of scope until the algebraic Linked Cluster
Theorem is done (see `notes/roadmaps/second-quantization.md`'s design principles). Creation and
annihilation operators, with their sign factors, come next (`CreationAnnihilation.lean`).
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

@[simp]
theorem basisState_ne_zero (n : Occupation Mode) : basisState n ≠ 0 :=
  Common.basisState_ne_zero n

theorem basisState_injective : Function.Injective (basisState : Occupation Mode → _) :=
  Common.basisState_injective

/-- Basis vectors are injective on all fermionic occupation states. -/
theorem basisState_injOn : Set.InjOn (basisState : Occupation Mode → _) Set.univ := by
  change Set.InjOn
    (Common.basisState : Occupation Mode → Common.AlgebraicFock (Occupation Mode)) Set.univ
  exact Common.basisState_injOn

/-- The fermionic occupation-number basis vectors are linearly independent. -/
theorem basisState_linearIndependent :
    LinearIndependent ℂ (basisState : Occupation Mode → OccupationFock Mode) := by
  change LinearIndependent ℂ
    (Common.basisState : Occupation Mode → Common.AlgebraicFock (Occupation Mode))
  exact Common.basisState_linearIndependent

/-- Two linear maps out of `OccupationFock Mode` that agree on every basis state are equal —
the basis-level facts proved in `CreationAnnihilation.lean`/`CanonicalAnticommutationRelations.lean`
suffice to establish the operator identities. -/
theorem linearMap_ext_basisState
    {f g : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode}
    (h : ∀ n, f (basisState n) = g (basisState n)) : f = g :=
  Common.linearMap_ext_basisState h

end Fermionic
end SecondQuantization
