import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Statistics
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Imaginary-time ordering `T_τ`, generic over the occupation-state type

Phase 9, step 2 (`notes/roadmaps/second-quantization.md`): imaginary-time ordering of a pair of
operators at (generally distinct) imaginary times. Time ordering itself does not depend on
`imaginaryTimeEvolve`, or on which concrete occupation-state type the operators act on — it
orders whatever two already-time-labelled `AlgebraicFock Config` endomorphisms it is given, using
only `LinearMap.comp` and scalar multiplication — so it is extracted here, generic over `Config`,
rather than duplicated per statistics. `Fermionic/ThermalTimeOrdering.lean` and
`Bosonic/ThermalTimeOrdering.lean` are thin wrappers fixing `Config` to `FermionOccupation
Mode`/`Occupation Mode` *and* the statistics to `Statistics.fermion`/`Statistics.boson`, so
downstream files no longer need to spell out `Statistics.zetaInt Statistics.fermion` at every call
site.

Two layers, mirroring `Common/ExchangeCommutator.lean`'s `zetaCommutator`/`exchangeCommutator`
split:

- **`zetaTimeOrderedProduct ζ A B τA τB`** takes a raw `ζ : ℤ`. This is the general-purpose form —
  nothing here forces `ζ ∈ {-1, 1}` — used when a caller already has a bare exchange sign in hand
  (e.g. mid-proof after unfolding `Statistics.zetaInt`).
- **`timeOrderedProduct s A B τA τB`**, for a quantum statistics `s : Statistics`, specializes
  `ζ := s.zetaInt`. This is the form callers should reach for once a `Statistics` value is in
  hand, and is what `Fermionic/Bosonic` fix to their own statistics below.

`T_τ[A(τ_A) B(τ_B)] := θ(τ_A - τ_B) A(τ_A) B(τ_B) + ζ · θ(τ_B - τ_A) B(τ_B) A(τ_A)`: later time to
the left, picking up a sign `ζ` on every operator swap needed to enforce that ordering — the
standard finite-temperature time-ordering convention. **`θ(0) := 1/2`**: at equal times
`τ_A = τ_B` this symmetrizes the two branches, `T_τ[A(τ)B(τ)] = ½(A(τ)B(τ) + ζ B(τ)A(τ))`, rather
than picking either one.

**Scope of the exchange-sign convention.** `timeOrderedProduct_swap`'s claim that swapping the
operator pair costs exactly `s.zetaInt` is the statement appropriate for *elementary*
creation/annihilation operators (or, more generally, any pair of operators that are each
individually "odd"/"even" matching `s`'s exchange parity) — it is not a claim about *arbitrary*
linear endomorphisms `A`, `B`. A composite operator built from an even number of fermionic
creation/annihilation operators (e.g. the number operator `N_i`) does not pick up a `-1` when
swapped past another such operator; nothing in this file's types enforces that distinction, so
callers are responsible for only invoking `timeOrderedProduct_swap` on operators whose exchange
parity genuinely matches `s`.
-/

namespace SecondQuantization
namespace Common

/-- **The `ζ`-parameterized imaginary-time-ordered product** of two operators `A`, `B` at
imaginary times `τ_A`, `τ_B`, for a raw exchange sign `ζ : ℤ`: the later time acts first
(leftmost), picking up a sign `ζ` when the times must be swapped from their given argument order,
and the two orderings symmetrized (`θ(0) = 1/2`) at equal times. See the module docstring for
`timeOrderedProduct`, the statistics-indexed form callers should prefer. -/
noncomputable def zetaTimeOrderedProduct {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  if τB < τA then A.comp B
  else if τA < τB then (ζ : ℂ) • (B.comp A)
  else (2⁻¹ : ℂ) • (A.comp B + (ζ : ℂ) • (B.comp A))

theorem zetaTimeOrderedProduct_of_gt {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τB < τA) :
    zetaTimeOrderedProduct ζ A B τA τB = A.comp B := by
  rw [zetaTimeOrderedProduct, if_pos h]

theorem zetaTimeOrderedProduct_of_lt {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τA < τB) :
    zetaTimeOrderedProduct ζ A B τA τB = (ζ : ℂ) • (B.comp A) := by
  rw [zetaTimeOrderedProduct, if_neg (not_lt.2 h.le), if_pos h]

@[simp]
theorem zetaTimeOrderedProduct_self_time {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    zetaTimeOrderedProduct ζ A B τ τ = (2⁻¹ : ℂ) • (A.comp B + (ζ : ℂ) • (B.comp A)) := by
  rw [zetaTimeOrderedProduct, if_neg (lt_irrefl τ), if_neg (lt_irrefl τ)]

/-- **Swapping the pair of operators (with their times) and negating by `ζ` returns the same
time-ordered product**: `T_τ[B(τ_B) A(τ_A)] = ζ · T_τ[A(τ_A) B(τ_B)]`, given `ζ² = 1` — including
at equal times, since the `θ(0) = 1/2` convention symmetrizes exactly enough to make this hold
unconditionally. See the module docstring's scope note: appropriate for elementary
creation/annihilation-type operators, not arbitrary `A`, `B`. -/
theorem zetaTimeOrderedProduct_swap {Config : Type*} {ζ : ℤ} (hζ : ζ * ζ = 1)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    zetaTimeOrderedProduct ζ B A τB τA = (ζ : ℂ) • zetaTimeOrderedProduct ζ A B τA τB := by
  have hζC : (ζ : ℂ) * (ζ : ℂ) = 1 := by exact_mod_cast hζ
  rcases lt_trichotomy τA τB with hlt | heq | hlt
  · rw [zetaTimeOrderedProduct_of_gt ζ B A hlt, zetaTimeOrderedProduct_of_lt ζ A B hlt, smul_smul,
      hζC, one_smul]
  · subst heq
    rw [zetaTimeOrderedProduct_self_time, zetaTimeOrderedProduct_self_time]
    rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      mul_comm (ζ : ℂ) (2⁻¹ : ℂ), mul_assoc, hζC, mul_one]
    abel
  · rw [zetaTimeOrderedProduct_of_lt ζ B A hlt, zetaTimeOrderedProduct_of_gt ζ A B hlt]

/-- **The statistics-indexed imaginary-time-ordered product**, `zetaTimeOrderedProduct`
specialized to `ζ := s.zetaInt` for a quantum statistics `s` — the form callers should reach for
once a `Statistics` value is in hand, rather than passing a raw `ζ : ℤ` constant. -/
noncomputable def timeOrderedProduct {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  zetaTimeOrderedProduct (s.zetaInt) A B τA τB

theorem timeOrderedProduct_of_gt {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct s A B τA τB = A.comp B :=
  zetaTimeOrderedProduct_of_gt s.zetaInt A B h

theorem timeOrderedProduct_of_lt {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct s A B τA τB = (s.zetaInt : ℂ) • (B.comp A) :=
  zetaTimeOrderedProduct_of_lt s.zetaInt A B h

@[simp]
theorem timeOrderedProduct_self_time {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    timeOrderedProduct s A B τ τ = (2⁻¹ : ℂ) • (A.comp B + (s.zetaInt : ℂ) • (B.comp A)) :=
  zetaTimeOrderedProduct_self_time s.zetaInt A B τ

/-- **Swapping the pair of operators (with their times) and negating by the exchange sign returns
the same time-ordered product**: `T_τ[B(τ_B) A(τ_A)] = s.zetaInt · T_τ[A(τ_A) B(τ_B)]`. Unlike
`zetaTimeOrderedProduct_swap`, no `ζ² = 1` hypothesis is needed — `Statistics.zeta_sq` supplies it
automatically for every `s`. See the module docstring's scope note on which operators this
applies to. -/
theorem timeOrderedProduct_swap {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    timeOrderedProduct s B A τB τA = (s.zetaInt : ℂ) • timeOrderedProduct s A B τA τB :=
  zetaTimeOrderedProduct_swap (Statistics.zeta_sq s) A B τA τB

end Common
end SecondQuantization
