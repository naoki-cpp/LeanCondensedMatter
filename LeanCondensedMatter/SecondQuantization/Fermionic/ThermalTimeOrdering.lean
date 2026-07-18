import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.TimeOrdering

set_option linter.style.header false

/-!
# Imaginary-time ordering `T_τ`, specialized to the fermionic Fock space

Phase 9, step 2 (`notes/roadmaps/second-quantization.md`): a thin wrapper specializing
`Common.TimeOrdering.lean`'s `Common.timeOrderedProduct` to `FockSpaceFermionic Mode`, keeping the
statistics-agnostic implementation in `Common/` (time ordering itself doesn't depend on
`imaginaryTimeEvolve` or on which concrete occupation-state type the operators act on) while
preserving this file's own public names — `ThermalGreenFunction.lean`, `ThermalContraction.lean`,
and `Fermionic/FreeTwoPointFunction.lean` all call `timeOrderedProduct` unqualified, and are
unaffected by this refactor. See `Bosonic/ThermalTimeOrdering.lean` for the bosonic mirror.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode]

/-- **The imaginary-time-ordered product** of two operators `A`, `B` at imaginary times `τ_A`,
`τ_B`, with exchange sign `ζ : ℤ` (`Statistics.zetaInt`): the later time acts first (leftmost),
picking up a sign `ζ` when the times must be swapped from their given argument order, and the two
orderings symmetrized (`θ(0) = 1/2`) at equal times. -/
noncomputable def timeOrderedProduct (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τA τB : ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Common.timeOrderedProduct ζ A B τA τB

theorem timeOrderedProduct_of_gt (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct ζ A B τA τB = A.comp B :=
  Common.timeOrderedProduct_of_gt ζ A B h

theorem timeOrderedProduct_of_lt (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct ζ A B τA τB = (ζ : ℂ) • (B.comp A) :=
  Common.timeOrderedProduct_of_lt ζ A B h

@[simp]
theorem timeOrderedProduct_self_time (ζ : ℤ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ) :
    timeOrderedProduct ζ A B τ τ = (2⁻¹ : ℂ) • (A.comp B + (ζ : ℂ) • (B.comp A)) :=
  Common.timeOrderedProduct_self_time ζ A B τ

/-- **Swapping the pair of operators (with their times) and negating for fermions returns the
same time-ordered product**: `T_τ[B(τ_B) A(τ_A)] = ζ · T_τ[A(τ_A) B(τ_B)]`, given `ζ² = 1`
(satisfied by `Statistics.zetaInt`, `zeta_sq`) — including at equal times, since the `θ(0) = 1/2`
convention symmetrizes exactly enough to make this hold unconditionally. This is the
operator-level statement that swapping two operators inside a time-ordered product costs exactly
the exchange sign. -/
theorem timeOrderedProduct_swap {ζ : ℤ} (hζ : ζ * ζ = 1)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τA τB : ℝ) :
    timeOrderedProduct ζ B A τB τA = (ζ : ℂ) • timeOrderedProduct ζ A B τA τB :=
  Common.timeOrderedProduct_swap hζ A B τA τB

end SecondQuantization
