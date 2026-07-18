import LeanCondensedMatter.SecondQuantization.Fermionic.FockSpace
import LeanCondensedMatter.SecondQuantization.Common.TimeOrdering

set_option linter.style.header false

/-!
# Imaginary-time ordering `T_τ`, specialized to the fermionic Fock space

The `ThermalTimeOrdering` filename is historical: this module defines imaginary-time ordering and
does not introduce a thermal state, weight, or inverse temperature.

Phase 9, step 2 (`notes/roadmaps/second-quantization.md`): a thin wrapper fixing
`Common.TimeOrdering.lean`'s `Common.timeOrderedProduct` to `FockSpaceFermionic Mode` *and* to
`Statistics.fermion` — time ordering itself depends on neither `imaginaryTimeEvolve` nor the
concrete occupation-state type, so this file only imports `FockSpace.lean`, not
`ImaginaryTimeEvolution.lean`. Fixing the statistics (rather than taking a `Statistics`/`ζ`
parameter) means callers never need to spell out `Statistics.zetaInt Statistics.fermion`, and
downstream files (`ThermalGreenFunction.lean`, `ThermalContraction.lean`,
`Fermionic/FreeTwoPointFunction.lean`) call `timeOrderedProduct A B τA τB` directly. See
`Bosonic/ThermalTimeOrdering.lean` for the bosonic mirror, and `Common/TimeOrdering.lean`'s module
docstring for the scope note on which operators the exchange-sign convention below applies to
(elementary creation/annihilation-type operators, not arbitrary `A`, `B`).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode]

/-- **The imaginary-time-ordered product** of two operators `A`, `B` at imaginary times `τ_A`,
`τ_B`: the later time acts first (leftmost), picking up the fermionic exchange sign `-1` when the
times must be swapped from their given argument order, and the two orderings symmetrized
(`θ(0) = 1/2`) at equal times. -/
noncomputable def timeOrderedProduct
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τA τB : ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Common.timeOrderedProduct Statistics.fermion A B τA τB

theorem timeOrderedProduct_of_gt
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {τA τB : ℝ} (h : τB < τA) :
    timeOrderedProduct A B τA τB = A.comp B :=
  Common.timeOrderedProduct_of_gt Statistics.fermion A B h

theorem timeOrderedProduct_of_lt
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) {τA τB : ℝ} (h : τA < τB) :
    timeOrderedProduct A B τA τB = (-1 : ℂ) • (B.comp A) := by
  change Common.timeOrderedProduct Statistics.fermion A B τA τB = (-1 : ℂ) • (B.comp A)
  rw [Common.timeOrderedProduct_of_lt Statistics.fermion A B h, Statistics.zetaInt_fermion,
    Int.cast_neg, Int.cast_one]

@[simp]
theorem timeOrderedProduct_self_time
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τ : ℝ) :
    timeOrderedProduct A B τ τ = (2⁻¹ : ℂ) • (A.comp B + (-1 : ℂ) • (B.comp A)) := by
  change Common.timeOrderedProduct Statistics.fermion A B τ τ =
    (2⁻¹ : ℂ) • (A.comp B + (-1 : ℂ) • (B.comp A))
  rw [Common.timeOrderedProduct_self_time Statistics.fermion A B τ, Statistics.zetaInt_fermion,
    Int.cast_neg, Int.cast_one]

/-- **Swapping the pair of operators (with their times) and negating returns the same
time-ordered product**: `T_τ[B(τ_B) A(τ_A)] = -T_τ[A(τ_A) B(τ_B)]`. See
`Common/TimeOrdering.lean`'s module docstring for the scope note on which operators this applies
to. -/
theorem timeOrderedProduct_swap
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (τA τB : ℝ) :
    timeOrderedProduct B A τB τA = (-1 : ℂ) • timeOrderedProduct A B τA τB := by
  change Common.timeOrderedProduct Statistics.fermion B A τB τA =
    (-1 : ℂ) • Common.timeOrderedProduct Statistics.fermion A B τA τB
  rw [Common.timeOrderedProduct_swap Statistics.fermion A B τA τB, Statistics.zetaInt_fermion,
    Int.cast_neg, Int.cast_one]

end SecondQuantization
