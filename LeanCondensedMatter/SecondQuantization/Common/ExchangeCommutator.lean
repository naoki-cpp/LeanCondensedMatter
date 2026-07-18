import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Statistics

set_option linter.style.header false

/-!
# The `ζ`-commutator, and its statistics-indexed specialization

Groundwork for the general (fermionic *and* bosonic) finite-temperature Bloch–de Dominicis theorem
(`notes/roadmaps/second-quantization.md`): the reordering identities
`Fermionic/FreeTwoPointFunction.lean`'s `annihilate_comp_create_self` (`c_i c_i† = id - N_i`, from
CAR's *anti*commutator `{c_i, c_i†} = id`) and the bosonic analogue `a_i a_i† = id + N_i` (from
CCR's *ordinary* commutator `[a_i, a_i†] = id`) are the same algebraic fact once the
`+`-vs-`-` distinction is absorbed into `Statistics.zetaInt`'s sign `ζ = -1` (fermion) / `ζ = +1`
(boson): both are instances of `[a_i, a_i†]_ζ = id` for the **`ζ`-commutator**
`[A, B]_ζ := A∘B - ζ•(B∘A)`, which specializes to the ordinary commutator at `ζ = 1` and to the
anticommutator at `ζ = -1`.

**Naming note.** This is *not* the graded commutator of a `ℤ`/`ℤ₂`-graded algebra in the usual
sense (`[A, B]_gr := AB - (-1)^{|A||B|} BA`, where the sign is determined by the operators' *own*
degrees). Here `ζ` is a single fixed constant applied uniformly to every pair `A, B`, indexing the
*ambient exchange statistics* rather than a per-operator grading — hence `zetaCommutator`,
specialized to a statistics-indexed `exchangeCommutator` below, not `gradedCommutator`.

**Nor is this a *contraction*** in the Wick-theorem sense (a thermal two-point function, a
`ℂ`-number like `⟨T_τ c_i c_j†⟩₀` — see `Fermionic/FreeTwoPointFunction.lean`'s
`freeGibbsExpectation_annihilate_comp_create`/`_create_comp_annihilate`, which *are* contraction
kernels). `comp_eq_id_add_of_zetaCommutator_eq_id` below is an *operator-level reordering
identity* — it rewrites `A∘B` in terms of `B∘A`, with no state or expectation value involved.

This file only sets up the two-operator algebra; it does not touch `Fermionic`/`Bosonic` — those
still keep their own concrete `anticomm`/`comm`, CAR/CCR proofs, and named reordering theorems
(`exchangeCommutator` is a *presentation* of the same fact, not a replacement for the
statistics-specific basis-level proofs that establish it).
-/

namespace SecondQuantization
namespace Common

/-- **The `ζ`-commutator**, `[A, B]_ζ := A∘B - ζ•(B∘A)`, for an arbitrary constant `ζ : ℂ`.
Specializes to the ordinary commutator `[A, B] = A∘B - B∘A` at `ζ = 1`, and to the anticommutator
`{A, B} = A∘B + B∘A` at `ζ = -1`. **Not** a graded commutator in the `ℤ`/`ℤ₂`-graded-algebra sense
(no per-operator degree is involved) — see the module docstring. -/
noncomputable def zetaCommutator {Config : Type*} (ζ : ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  A.comp B - ζ • (B.comp A)

/-- **The exchange commutator**, `zetaCommutator` specialized to `ζ := s.zetaInt` for a quantum
statistics `s` — `Statistics.zetaInt`'s `+1`/`-1` is genuinely what selects CCR vs. CAR, so this is
the form callers should reach for once a `Statistics` value is in hand, rather than passing a raw
`ζ : ℂ` constant. -/
noncomputable def exchangeCommutator {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  zetaCommutator (s.zetaInt : ℂ) A B

/-- **The reordering identity.** If `A`, `B` satisfy `[A, B]_ζ = id` (the unified shape of CAR's
`{c_i, c_i†} = id` at `ζ = -1` and CCR's `[a_i, a_i†] = id` at `ζ = 1`), then `A∘B` is `id` plus a
`ζ`-multiple of `B∘A` — e.g. `id - N_i` (fermion, `ζ = -1`) or `id + N_i` (boson, `ζ = 1`) when
`B∘A` is the number operator. Purely an operator identity, not a thermal contraction — see the
module docstring. -/
theorem comp_eq_id_add_of_zetaCommutator_eq_id {Config : Type*} (ζ : ℂ)
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : zetaCommutator ζ A B = LinearMap.id) :
    A.comp B = LinearMap.id + ζ • (B.comp A) := by
  have h' : A.comp B - ζ • (B.comp A) = LinearMap.id := by
    simpa [zetaCommutator] using h
  exact (sub_eq_iff_eq_add).mp h'

end Common
end SecondQuantization
