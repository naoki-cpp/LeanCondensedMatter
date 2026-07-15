import LeanCondensedMatter.SecondQuantization.FermionOccupation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic

set_option linter.style.header false

/-!
# Fermionic Fock space (algebraic)

Phase 3 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
algebraic (finite-particle, uncompleted) fermionic Fock space — the free `ℂ`-vector space on the
fermionic occupation-number basis `FermionOccupation Mode` (`FermionOccupation.lean`).

Deliberately algebraic only: no inner product, no Hilbert-space completion, no bounded/unbounded
operator theory. Those analytic questions are out of scope until the algebraic Linked Cluster
Theorem is done (see `notes/roadmaps/second-quantization.md`'s design principles). Creation and
annihilation operators, with their sign factors, come next
(`CreationAnnihilationFermionic.lean`).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode]

/-- **The algebraic fermionic Fock space.** The free `ℂ`-vector space on the basis
`FermionOccupation Mode` — finite `ℂ`-linear combinations of occupation-number states. An
`abbrev` so `Finsupp`'s own `AddCommGroup`/`Module ℂ` instances transfer automatically. -/
abbrev FockSpaceFermionic (Mode : Type*) [DecidableEq Mode] := FermionOccupation Mode →₀ ℂ

/-- **The basis vector** corresponding to occupation-number state `n`. -/
noncomputable def basisState (n : FermionOccupation Mode) : FockSpaceFermionic Mode :=
  Finsupp.single n 1

/-- **The Fock vacuum vector**, the basis vector of the empty occupation state. -/
noncomputable def fockVacuum : FockSpaceFermionic Mode := basisState fermionVacuum

@[simp]
theorem basisState_ne_zero (n : FermionOccupation Mode) : basisState n ≠ 0 :=
  Finsupp.single_ne_zero.2 one_ne_zero

theorem basisState_injective : Function.Injective (basisState : FermionOccupation Mode → _) :=
  fun _ _ h => Finsupp.single_left_injective one_ne_zero h

/-- Distinct occupation-number states give linearly-independent (in fact, orthogonal-support)
basis vectors: `basisState m` and `basisState n` never coincide for `m ≠ n`. -/
theorem basisState_injOn : Set.InjOn (basisState : FermionOccupation Mode → _) Set.univ :=
  fun _ _ _ _ h => basisState_injective h

end SecondQuantization
