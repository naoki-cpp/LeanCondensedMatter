import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Imaginary-time ordering `T_τ`, generic over the occupation-state type

Phase 9, step 2 (`notes/roadmaps/second-quantization.md`): imaginary-time ordering of a pair of
operators at (generally distinct) imaginary times. Time ordering itself does not depend on
`imaginaryTimeEvolve`, or on which concrete occupation-state type the operators act on — it
orders whatever two already-time-labelled `AlgebraicFock Config` endomorphisms it is given, using
only `LinearMap.comp` and scalar multiplication — so it is extracted here, generic over `Config`,
rather than duplicated per statistics.

`timeOrderedProduct s A B τA τB` takes the exchange sign from the quantum statistics
`s : Statistics` directly. This keeps the public API on the physically meaningful statistics
boundary rather than exposing a second raw-sign implementation layer.

`T_τ[A(τ_A) B(τ_B)] := θ(τ_A - τ_B) A(τ_A) B(τ_B) + ζ · θ(τ_B - τ_A) B(τ_B) A(τ_A)`: later time to
the left, picking up a sign `ζ = s.zetaInt` when the times must be swapped from their given
argument order — the standard finite-temperature time-ordering convention. **`θ(0) := 1/2`**: at
equal times `τ_A = τ_B` this symmetrizes the two branches,
`T_τ[A(τ)B(τ)] = ½(A(τ)B(τ) + ζ B(τ)A(τ))`, rather than picking either one.

**Scope of the exchange-sign convention.** `timeOrderedProduct_swap` is an algebraic identity that
holds for *arbitrary* `A`, `B` — it follows directly from the definition, with no restriction on
the operators. What is restricted is a *physical interpretation*: reading
`timeOrderedProduct Statistics.fermion A B τA τB` as *the* fermionic time-ordered product of `A`
and `B` is appropriate only when `A`, `B`'s exchange parity matches the chosen sign — i.e. for
elementary creation/annihilation operators, or more generally operators that are each
individually "odd"/"even" consistently with `s`. A composite operator built from an even number of
fermionic creation/annihilation operators (e.g. the number operator `N_i`) does not physically
pick up a `-1` when exchanged past another such operator, even though the *theorem*
`timeOrderedProduct_swap` still applies to it and correctly computes what this file's `-1`
convention assigns; nothing in this file's types enforces the parity-matching condition, so
callers are responsible for only relying on the *physical* fermionic-time-ordering reading when
that condition holds.
-/

namespace SecondQuantization
namespace Common

/-- **The statistics-indexed imaginary-time-ordered product** of two operators `A`, `B` at
imaginary times `τ_A`, `τ_B`: the later time acts first (leftmost), with exchange sign
`Statistics.zetaInt s`, and the two orderings are symmetrized at equal times. -/
noncomputable def timeOrderedProduct {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  if τB < τA then A.comp B
  else if τA < τB then (s.zetaInt : ℂ) • (B.comp A)
  else (2⁻¹ : ℂ) • (A.comp B + (s.zetaInt : ℂ) • (B.comp A))

theorem timeOrderedProduct_of_gt {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct s A B τA τB = A.comp B := by
  rw [timeOrderedProduct, if_pos h]

theorem timeOrderedProduct_of_lt {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct s A B τA τB = (s.zetaInt : ℂ) • (B.comp A) := by
  rw [timeOrderedProduct, if_neg (not_lt.2 h.le), if_pos h]

@[simp]
theorem timeOrderedProduct_self_time {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    timeOrderedProduct s A B τ τ =
      (2⁻¹ : ℂ) • (A.comp B + (s.zetaInt : ℂ) • (B.comp A)) := by
  rw [timeOrderedProduct, if_neg (lt_irrefl τ), if_neg (lt_irrefl τ)]

/-- **Swapping the pair of operators (with their times) and multiplying by the exchange sign
returns the same time-ordered product**:
`T_τ[B(τ_B) A(τ_A)] = s.zetaInt · T_τ[A(τ_A) B(τ_B)]`.
`Statistics.zeta_sq` supplies the fact that the exchange sign squares to one. See the module
docstring's scope note on which operators admit the usual physical reading. -/
theorem timeOrderedProduct_swap {Config : Type*} (s : Statistics)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    timeOrderedProduct s B A τB τA =
      (s.zetaInt : ℂ) • timeOrderedProduct s A B τA τB := by
  have hζC : (s.zetaInt : ℂ) * (s.zetaInt : ℂ) = 1 := by
    exact_mod_cast Statistics.zeta_sq s
  rcases lt_trichotomy τA τB with hlt | heq | hlt
  · rw [timeOrderedProduct_of_gt s B A hlt, timeOrderedProduct_of_lt s A B hlt, smul_smul,
      hζC, one_smul]
  · subst heq
    rw [timeOrderedProduct_self_time, timeOrderedProduct_self_time]
    rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      mul_comm (s.zetaInt : ℂ) (2⁻¹ : ℂ), mul_assoc, hζC, mul_one]
    abel
  · rw [timeOrderedProduct_of_lt s B A hlt, timeOrderedProduct_of_gt s A B hlt]

end Common
end SecondQuantization
