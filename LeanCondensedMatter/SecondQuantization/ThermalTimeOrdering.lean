import LeanCondensedMatter.SecondQuantization.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Statistics

set_option linter.style.header false

/-!
# Imaginary-time ordering `T_τ`

Phase 9, step 2 (`notes/roadmaps/second-quantization.md`): imaginary-time ordering of a pair of
operators at (generally distinct) imaginary times, the ingredient
`ImaginaryTimeEvolution.lean`'s `e^{τH₀}`/`imaginaryTimeEvolve` still lacks. Time ordering itself
does not depend on `imaginaryTimeEvolve` — it orders whatever two already-time-labelled operators
it is given — but its intended use is on `imaginaryTimeEvolve ε τ A` for various `A`, `τ`, feeding
directly into `ThermalGreenFunction.lean`'s two-point function.

`T_τ[A(τ_A) B(τ_B)] := θ(τ_A - τ_B) A(τ_A) B(τ_B) + ζ · θ(τ_B - τ_A) B(τ_B) A(τ_A)`, where `ζ` is
`Statistics.zetaInt` (`-1` for fermions, `+1` for bosons): later time to the left, picking up a
sign `ζ` on every operator swap needed to enforce that ordering — the standard finite-temperature
time-ordering convention. At equal times `τ_A = τ_B` this is a *definition*, not a derived
equality of the two branches (which need not agree); it always resolves to the `τ_B ≤ τ_A` branch
here.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode]

/-- **The imaginary-time-ordered product** of two operators `A`, `B` at imaginary times `τ_A`,
`τ_B`, with exchange sign `ζ : ℤ` (`Statistics.zetaInt`): the later time acts first (leftmost),
picking up a sign `ζ` when the times must be swapped from their given argument order. -/
noncomputable def timeOrderedProduct (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τA τB : ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  if τB ≤ τA then A.comp B else (ζ : ℂ) • (B.comp A)

theorem timeOrderedProduct_of_le (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {τA τB : ℝ} (h : τB ≤ τA) :
    timeOrderedProduct ζ A B τA τB = A.comp B := by
  rw [timeOrderedProduct, if_pos h]

theorem timeOrderedProduct_of_lt (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct ζ A B τA τB = (ζ : ℂ) • (B.comp A) := by
  rw [timeOrderedProduct, if_neg (not_le.2 h)]

@[simp]
theorem timeOrderedProduct_self_time (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ) :
    timeOrderedProduct ζ A B τ τ = A.comp B :=
  timeOrderedProduct_of_le ζ A B le_rfl

/-- **Swapping the pair of operators (with their times) and negating for fermions returns the
same time-ordered product**, away from equal times: `T_τ[B(τ_B) A(τ_A)] = ζ · T_τ[A(τ_A) B(τ_B)]`
whenever `τ_A ≠ τ_B` and `ζ² = 1` (satisfied by `Statistics.zetaInt`, `zeta_sq`). This is the
operator-level statement that swapping two operators inside a time-ordered product costs exactly
the exchange sign. -/
theorem timeOrderedProduct_swap {ζ : ℤ} (hζ : ζ * ζ = 1)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {τA τB : ℝ} (h : τA ≠ τB) :
    timeOrderedProduct ζ B A τB τA = (ζ : ℂ) • timeOrderedProduct ζ A B τA τB := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [timeOrderedProduct_of_le ζ B A hlt.le, timeOrderedProduct_of_lt ζ A B hlt, smul_smul]
    have hζC : (ζ : ℂ) * (ζ : ℂ) = 1 := by exact_mod_cast hζ
    rw [hζC, one_smul]
  · rw [timeOrderedProduct_of_lt ζ B A hlt, timeOrderedProduct_of_le ζ A B hlt.le]

end SecondQuantization
