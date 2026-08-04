import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore

set_option linter.style.header false

/-!
# Free-evolution time-ordered two-point functionals

`weightedFreeTwoPointFunction ε w i j τ τ' := -⟨T_τ c_i(τ) c_j†(τ')⟩_w` combines the free
imaginary-time evolution with an arbitrary normalized occupation-diagonal weight `w`.

This is not the physical free Gibbs Green function until `w` is the free Boltzmann weight associated
with the same `ε`. The specialization `freeGibbsGreenFunction` below fixes exactly that weight.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The fermionic two-point (imaginary-)time-ordered correlator**,
`G_{ij}(τ, τ') := -⟨T_τ c_i(τ) c_j†(τ')⟩_w`, for the free Hamiltonian's imaginary-time evolution
`c_i(τ) := imaginaryTimeEvolve ε τ (annihilate i)`, `c_j†(τ') := imaginaryTimeEvolve ε τ'
(create j)`, and an arbitrary weight `w`. -/
noncomputable def weightedFreeTwoPointFunction (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - Common.normalizedWeightedDiagonal w
      (Common.timeOrderedProduct Common.Statistics.fermion
        (imaginaryTimeEvolve ε τ (annihilate i)) (imaginaryTimeEvolve ε τ' (create j)) τ τ')

/-- **For `τ' < τ`**, time-ordering already has `c_i(τ)` to the left: `G_{ij}(τ, τ') =
-⟨c_i(τ) c_j†(τ')⟩_w`. -/
theorem weightedFreeTwoPointFunction_of_gt (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode)
    {τ τ' : ℝ} (h : τ' < τ) :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      - Common.normalizedWeightedDiagonal w
          ((imaginaryTimeEvolve ε τ (annihilate i)).comp
            (imaginaryTimeEvolve ε τ' (create j))) := by
  rw [weightedFreeTwoPointFunction, Common.timeOrderedProduct_of_gt Common.Statistics.fermion _ _ h]

/-- **For `τ < τ'`**, time-ordering swaps to `c_j†(τ')` on the left, picking up the fermionic
exchange sign `-1`, which cancels the definition's outer `-1`: `G_{ij}(τ, τ') =
+⟨c_j†(τ') c_i(τ)⟩_w`. -/
theorem weightedFreeTwoPointFunction_of_lt (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode) {τ τ' : ℝ} (h : τ < τ') :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      Common.normalizedWeightedDiagonal w
        ((imaginaryTimeEvolve ε τ' (create j)).comp
          (imaginaryTimeEvolve ε τ (annihilate i))) := by
  rw [weightedFreeTwoPointFunction, Common.timeOrderedProduct_of_lt Common.Statistics.fermion _ _ h,
    Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one, neg_one_smul,
    Common.normalizedWeightedDiagonal, Common.weightedTrace]
  simp only [Common.matrixCoeff, LinearMap.neg_apply, Finsupp.neg_apply, mul_neg,
    Common.normalizedWeightedDiagonal, Common.weightedTrace, Finset.sum_neg_distrib, neg_div,
    neg_neg]

/-- **At equal times**, this selects the `θ(0) = 1/2` convention fixed by
`Common.timeOrderedProduct`: an average of the two one-sided orderings, not equality of the
fermionic Green function's one-sided limits. -/
theorem weightedFreeTwoPointFunction_self_time (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode) (τ : ℝ) :
    weightedFreeTwoPointFunction ε w i j τ τ =
      - Common.normalizedWeightedDiagonal w
          ((2⁻¹ : ℂ) • ((imaginaryTimeEvolve ε τ (annihilate i)).comp
              (imaginaryTimeEvolve ε τ (create j)) +
            (-1 : ℂ) •
              ((imaginaryTimeEvolve ε τ (create j)).comp
                (imaginaryTimeEvolve ε τ (annihilate i))))) := by
  rw [weightedFreeTwoPointFunction, Common.timeOrderedProduct_self_time Common.Statistics.fermion,
    Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]

/-- The free Gibbs two-point Green function, obtained by specializing the diagonal weight to the
free Boltzmann weight associated with the same one-particle energy `ε`. -/
noncomputable def freeGibbsGreenFunction (ε : Mode → ℝ) (β : ℝ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  weightedFreeTwoPointFunction ε (freeBoltzmannWeight ε β) i j τ τ'

end Fermionic
end SecondQuantization
