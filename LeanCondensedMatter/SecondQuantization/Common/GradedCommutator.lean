import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock

set_option linter.style.header false

/-!
# The `ζ`-graded commutator, generic over the exchange statistics

Groundwork for the general (fermionic *and* bosonic) finite-mode Wick/Bloch–de Dominicis theorem
(`notes/roadmaps/second-quantization.md`): the self-contraction identities
`Fermionic/FreeTwoPointFunction.lean`'s `annihilate_comp_create_self` (`c_i c_i† = id - N_i`, from
CAR's *anti*commutator `{c_i, c_i†} = id`) and the bosonic analogue `a_i a_i† = id + N_i` (from
CCR's *ordinary* commutator `[a_i, a_i†] = id`) are the same algebraic fact once the
`+`-vs-`-` distinction is absorbed into `Statistics.zetaInt`'s sign `ζ = -1` (fermion) / `ζ = +1`
(boson): both are instances of `[a_i, a_i†]_ζ = id` for the **`ζ`-graded commutator**
`[A, B]_ζ := A∘B - ζ•(B∘A)`, which specializes to the ordinary commutator at `ζ = 1` and to the
anticommutator at `ζ = -1`.

This file only sets up the two-operator algebra; it does not touch `Fermionic`/`Bosonic` — those
still keep their own concrete `anticomm`/`comm`, CAR/CCR proofs, and named self-contraction
theorems (`gradedCommutator` is a *presentation* of the same fact, not a replacement for the
statistics-specific basis-level proofs that establish it).
-/

namespace SecondQuantization
namespace Common

/-- **The `ζ`-graded commutator**, `[A, B]_ζ := A∘B - ζ•(B∘A)`. Specializes to the ordinary
commutator `[A, B] = A∘B - B∘A` at `ζ = 1`, and to the anticommutator `{A, B} = A∘B + B∘A` at
`ζ = -1` — `Statistics.zetaInt`'s two values. -/
noncomputable def gradedCommutator {Config : Type*} (ζ : ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  A.comp B - ζ • (B.comp A)

/-- **The self-contraction identity.** If `A`, `B` satisfy `[A, B]_ζ = id` (the unified shape of
CAR's `{c_i, c_i†} = id` at `ζ = -1` and CCR's `[a_i, a_i†] = id` at `ζ = 1`), then `A∘B` is
`id` plus a `ζ`-multiple of `B∘A` — e.g. `id - N_i` (fermion, `ζ = -1`) or `id + N_i` (boson,
`ζ = 1`) when `B∘A` is the number operator. -/
theorem selfContraction_of_gradedCommutator_eq_id {Config : Type*} (ζ : ℂ)
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : gradedCommutator ζ A B = LinearMap.id) :
    A.comp B = LinearMap.id + ζ • (B.comp A) := by
  rw [gradedCommutator, sub_eq_iff_eq_add] at h
  exact h

end Common
end SecondQuantization
