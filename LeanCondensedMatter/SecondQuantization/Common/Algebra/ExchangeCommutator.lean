import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics

set_option linter.style.header false

/-!
# The `ζ`-commutator and its statistics-indexed specialization

The reordering identities for fermionic and bosonic ladder operators have one common algebraic
shape. Fermionic CAR gives `c_i c_i† = id - c_i† c_i`, while bosonic CCR gives
`a_i a_i† = id + a_i† a_i`. The sign is encoded by `Statistics.zetaInt`: `-1` for fermions and
`+1` for bosons.

This module defines

`[A, B]_ζ := A ∘ B - ζ • (B ∘ A)`

and its statistics-indexed specialization. This is not the usual graded commutator of a graded
algebra: `ζ` is one fixed exchange-statistics sign rather than a sign computed from the individual
operator degrees.

It is also not a Wick contraction. A contraction is a scalar thermal two-point value, such as the
kernels in `Fermionic/Thermal/FreeGibbsGreenFunction.lean`; the declarations here are operator-level
reordering identities with no state or expectation value.
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

/-- **`zetaCommutator` is bilinear in scalar multiples**: `[c•A, d•B]_ζ = (c*d)•[A, B]_ζ` — direct
from `zetaCommutator`'s own definition via `LinearMap.smul_comp`/`LinearMap.comp_smul` and
`smul_smul`. Needed to extract the `Complex.exp` eigenvalue-shift scalars an `imaginaryTimeEvolve`-
dressed operator picks up, leaving only the bare (untime-evolved) commutator behind. -/
theorem zetaCommutator_smul_smul {Config : Type*} (ζ c d : ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    zetaCommutator ζ (c • A) (d • B) = (c * d) • zetaCommutator ζ A B := by
  simp only [zetaCommutator, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, smul_sub]
  congr 2 <;> ring

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
