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
`Bosonic/ThermalTimeOrdering.lean` are thin wrappers specializing `Config` to
`FermionOccupation Mode`/`Occupation Mode`, keeping their own public names (`timeOrderedProduct`
etc.) so downstream files (`ThermalGreenFunction.lean`, `ThermalContraction.lean`, ...) are
unaffected.

`T_τ[A(τ_A) B(τ_B)] := θ(τ_A - τ_B) A(τ_A) B(τ_B) + ζ · θ(τ_B - τ_A) B(τ_B) A(τ_A)`, where `ζ` is
`Statistics.zetaInt` (`-1` for fermions, `+1` for bosons): later time to the left, picking up a
sign `ζ` on every operator swap needed to enforce that ordering — the standard finite-temperature
time-ordering convention. **`θ(0) := 1/2`**: at equal times `τ_A = τ_B` this symmetrizes the two
branches, `T_τ[A(τ)B(τ)] = ½(A(τ)B(τ) + ζ B(τ)A(τ))`, rather than picking either one.
-/

namespace SecondQuantization
namespace Common

/-- **The imaginary-time-ordered product** of two operators `A`, `B` at imaginary times `τ_A`,
`τ_B`, with exchange sign `ζ : ℤ` (`Statistics.zetaInt`): the later time acts first (leftmost),
picking up a sign `ζ` when the times must be swapped from their given argument order, and the two
orderings symmetrized (`θ(0) = 1/2`) at equal times. -/
noncomputable def timeOrderedProduct {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  if τB < τA then A.comp B
  else if τA < τB then (ζ : ℂ) • (B.comp A)
  else (2⁻¹ : ℂ) • (A.comp B + (ζ : ℂ) • (B.comp A))

theorem timeOrderedProduct_of_gt {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct ζ A B τA τB = A.comp B := by
  rw [timeOrderedProduct, if_pos h]

theorem timeOrderedProduct_of_lt {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct ζ A B τA τB = (ζ : ℂ) • (B.comp A) := by
  rw [timeOrderedProduct, if_neg (not_lt.2 h.le), if_pos h]

@[simp]
theorem timeOrderedProduct_self_time {Config : Type*} (ζ : ℤ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    timeOrderedProduct ζ A B τ τ = (2⁻¹ : ℂ) • (A.comp B + (ζ : ℂ) • (B.comp A)) := by
  rw [timeOrderedProduct, if_neg (lt_irrefl τ), if_neg (lt_irrefl τ)]

/-- **Swapping the pair of operators (with their times) and negating for fermions returns the
same time-ordered product**: `T_τ[B(τ_B) A(τ_A)] = ζ · T_τ[A(τ_A) B(τ_B)]`, given `ζ² = 1`
(satisfied by `Statistics.zetaInt`, `zeta_sq`) — including at equal times, since the `θ(0) = 1/2`
convention symmetrizes exactly enough to make this hold unconditionally. This is the
operator-level statement that swapping two operators inside a time-ordered product costs exactly
the exchange sign. -/
theorem timeOrderedProduct_swap {Config : Type*} {ζ : ℤ} (hζ : ζ * ζ = 1)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τA τB : ℝ) :
    timeOrderedProduct ζ B A τB τA = (ζ : ℂ) • timeOrderedProduct ζ A B τA τB := by
  have hζC : (ζ : ℂ) * (ζ : ℂ) = 1 := by exact_mod_cast hζ
  rcases lt_trichotomy τA τB with hlt | heq | hlt
  · rw [timeOrderedProduct_of_gt ζ B A hlt, timeOrderedProduct_of_lt ζ A B hlt, smul_smul, hζC,
      one_smul]
  · subst heq
    rw [timeOrderedProduct_self_time, timeOrderedProduct_self_time]
    rw [smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      mul_comm (ζ : ℂ) (2⁻¹ : ℂ), mul_assoc, hζC, mul_one]
    abel
  · rw [timeOrderedProduct_of_lt ζ B A hlt, timeOrderedProduct_of_gt ζ A B hlt]

end Common
end SecondQuantization
