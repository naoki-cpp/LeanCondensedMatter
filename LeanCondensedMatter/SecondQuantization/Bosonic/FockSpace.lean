import LeanCondensedMatter.SecondQuantization.Bosonic.Occupation
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# Bosonic Fock space (algebraic)

Phase B1 of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): the algebraic
(finite-particle, uncompleted) bosonic Fock space — the free `ℂ`-vector space on the bosonic
occupation-number basis `Occupation Mode` (`BosonOccupation.lean`).

The Fock-space and operator declarations here live under `namespace SecondQuantization.Bosonic`,
distinct from the fermionic line's plain `SecondQuantization` namespace: `basisState`, `create`,
`annihilate`, etc. all have fermionic
namesakes in `FockSpaceFermionic.lean`/`CreationAnnihilationFermionic.lean`, and the bosonic
theory is genuinely different (occupation numbers are unbounded, so `FockSpaceBosonic Mode`, while
still algebraic here, is expected to be infinite-dimensional even for a finite mode set — unlike
the fermionic `2^|Mode|`-dimensional case). Deliberately algebraic only, exactly as in the
fermionic line: no inner product, no Hilbert-space completion, no bounded/unbounded operator
theory, and — since occupation-number sums here range over all of `Occupation Mode` rather than a
`Fintype` — no thermal trace/partition-function machinery either; see the module docstring's
"What remains" note in `notes/roadmaps/second-quantization.md` for why that needs its own staged
approach (finite occupation cutoffs first) rather than reusing the fermionic finite-sum API
directly.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **The algebraic bosonic Fock space.** The free `ℂ`-vector space on the basis
`Occupation Mode` — finite `ℂ`-linear combinations of occupation-number states. An `abbrev` so
`Finsupp`'s own `AddCommGroup`/`Module ℂ` instances transfer automatically. -/
abbrev FockSpaceBosonic (Mode : Type*) [DecidableEq Mode] := Occupation Mode →₀ ℂ

/-- **The basis vector** corresponding to occupation-number state `n`. -/
noncomputable def basisState (n : Occupation Mode) : FockSpaceBosonic Mode :=
  Finsupp.single n 1

/-- **The Fock vacuum vector**, the basis vector of the zero-occupation state. -/
noncomputable def fockVacuum : FockSpaceBosonic Mode := basisState vacuum

@[simp]
theorem basisState_ne_zero (n : Occupation Mode) : basisState n ≠ 0 :=
  Finsupp.single_ne_zero.2 one_ne_zero

theorem basisState_injective : Function.Injective (basisState : Occupation Mode → _) :=
  fun _ _ h => Finsupp.single_left_injective one_ne_zero h

/-- Distinct occupation-number states give distinct basis vectors: `basisState m` and
`basisState n` never coincide for `m ≠ n`. Their `Finsupp` supports are disjoint singletons. -/
theorem basisState_injOn : Set.InjOn (basisState : Occupation Mode → _) Set.univ :=
  fun _ _ _ _ h => basisState_injective h

/-- The basis vectors are in fact linearly independent, as `Finsupp.single`'s standard basis
family always is. -/
theorem basisState_linearIndependent :
    LinearIndependent ℂ (basisState : Occupation Mode → FockSpaceBosonic Mode) := by
  change LinearIndependent ℂ (fun n => Finsupp.single n (1 : ℂ))
  exact Finsupp.basisSingleOne.linearIndependent

end Bosonic
end SecondQuantization
