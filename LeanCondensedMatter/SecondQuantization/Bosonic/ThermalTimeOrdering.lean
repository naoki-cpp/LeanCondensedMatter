import LeanCondensedMatter.SecondQuantization.Bosonic.FockSpace
import LeanCondensedMatter.SecondQuantization.Common.TimeOrdering

set_option linter.style.header false

/-!
# Imaginary-time ordering `T_τ`, specialized to the bosonic Fock space

The bosonic mirror of `Fermionic/ThermalTimeOrdering.lean`: a thin wrapper specializing
`Common/TimeOrdering.lean`'s `Common.timeOrderedProduct` to `FockSpaceBosonic Mode`. Nothing here
is fermion-specific — the definition and every theorem below are identical to the fermionic file
up to the type of the operators, `ζ` taking the value `Statistics.zetaInt Statistics.boson = 1`
where relevant — so this file exists purely for symmetry with the fermionic line's file layout
(`notes/roadmaps/second-quantization.md`'s `Common/` design principle), not because anything in
the bosonic line consumes `timeOrderedProduct` yet.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **The imaginary-time-ordered product** of two operators `A`, `B` at imaginary times `τ_A`,
`τ_B`, with exchange sign `ζ : ℤ` (`Statistics.zetaInt`): the later time acts first (leftmost),
picking up a sign `ζ` when the times must be swapped from their given argument order, and the two
orderings symmetrized (`θ(0) = 1/2`) at equal times. -/
noncomputable def timeOrderedProduct (ζ : ℤ)
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) (τA τB : ℝ) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Common.timeOrderedProduct ζ A B τA τB

theorem timeOrderedProduct_of_gt (ζ : ℤ)
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct ζ A B τA τB = A.comp B :=
  Common.timeOrderedProduct_of_gt ζ A B h

theorem timeOrderedProduct_of_lt (ζ : ℤ)
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct ζ A B τA τB = (ζ : ℂ) • (B.comp A) :=
  Common.timeOrderedProduct_of_lt ζ A B h

@[simp]
theorem timeOrderedProduct_self_time (ζ : ℤ)
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) (τ : ℝ) :
    timeOrderedProduct ζ A B τ τ = (2⁻¹ : ℂ) • (A.comp B + (ζ : ℂ) • (B.comp A)) :=
  Common.timeOrderedProduct_self_time ζ A B τ

/-- **Swapping the pair of operators (with their times) returns the same time-ordered product**
up to the exchange sign: `T_τ[B(τ_B) A(τ_A)] = ζ · T_τ[A(τ_A) B(τ_B)]`, given `ζ² = 1` (satisfied
by `Statistics.zetaInt`, `zeta_sq`) — including at equal times, since the `θ(0) = 1/2` convention
symmetrizes exactly enough to make this hold unconditionally. -/
theorem timeOrderedProduct_swap {ζ : ℤ} (hζ : ζ * ζ = 1)
    (A B : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) (τA τB : ℝ) :
    timeOrderedProduct ζ B A τB τA = (ζ : ℂ) • timeOrderedProduct ζ A B τA τB :=
  Common.timeOrderedProduct_swap hζ A B τA τB

end Bosonic
end SecondQuantization
