import LeanCondensedMatter.SecondQuantization.Fermionic.Occupation
import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock

set_option linter.style.header false

/-!
# Fermionic Fock space (algebraic)

Phase 3 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
algebraic (finite-particle, uncompleted) fermionic Fock space — the free `ℂ`-vector space on the
fermionic occupation-number basis `FermionOccupation Mode` (`FermionOccupation.lean`).

Built directly on `Common.AlgebraicFock`: `FockSpaceFermionic Mode := Common.AlgebraicFock
(FermionOccupation Mode)`, with `basisState`/`linearMap_ext_basisState` reusing the generic
`Common` versions rather than re-proving them (fermionic-specific facts like `basisState_injOn`
and the vacuum still live here). Deliberately algebraic only: no inner product, no Hilbert-space
completion, no bounded/unbounded operator theory. Those analytic questions are out of scope until
the algebraic Linked Cluster Theorem is done (see `notes/roadmaps/second-quantization.md`'s design
principles). Creation and annihilation operators, with their sign factors, come next
(`CreationAnnihilation.lean`).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode]

/-- **The algebraic fermionic Fock space.** The free `ℂ`-vector space on the basis
`FermionOccupation Mode` — finite `ℂ`-linear combinations of occupation-number states, reusing
`Common.AlgebraicFock`. -/
abbrev FockSpaceFermionic (Mode : Type*) [DecidableEq Mode] :=
  Common.AlgebraicFock (FermionOccupation Mode)

/-- **The basis vector** corresponding to occupation-number state `n`. -/
noncomputable def basisState (n : FermionOccupation Mode) : FockSpaceFermionic Mode :=
  Common.basisState n

/-- **The Fock vacuum vector**, the basis vector of the empty occupation state. -/
noncomputable def fockVacuum : FockSpaceFermionic Mode := basisState fermionVacuum

@[simp]
theorem basisState_ne_zero (n : FermionOccupation Mode) : basisState n ≠ 0 :=
  Common.basisState_ne_zero n

theorem basisState_injective : Function.Injective (basisState : FermionOccupation Mode → _) :=
  Common.basisState_injective

/-- Distinct occupation-number states give linearly-independent (in fact, orthogonal-support)
basis vectors: `basisState m` and `basisState n` never coincide for `m ≠ n`. -/
theorem basisState_injOn : Set.InjOn (basisState : FermionOccupation Mode → _) Set.univ :=
  fun _ _ _ _ h => basisState_injective h

/-- Two linear maps out of `FockSpaceFermionic Mode` that agree on every basis state are equal —
the basis-level facts proved in `CreationAnnihilation.lean`/`CanonicalAnticommutationRelations.lean`
suffice to establish the operator identities. -/
theorem linearMap_ext_basisState {f g : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode}
    (h : ∀ n, f (basisState n) = g (basisState n)) : f = g :=
  Common.linearMap_ext_basisState h

end SecondQuantization
