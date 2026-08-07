import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.TwoPoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore

set_option linter.style.header false

/-!
# Free-evolution time-ordered two-point functionals

`weightedFreeTwoPointFunction ε w i j τ τ' := -⟨T_τ c_i(τ) c_j†(τ')⟩_w` applies an arbitrary
normalized occupation-diagonal weight `w` to the canonical free two-point operator from
`Fermionic/ImaginaryTime/TwoPoint.lean`.

This is not the physical free Gibbs Green function until `w` is the free Boltzmann weight associated
with the same `ε`. The specialization `freeGibbsGreenFunction` below fixes exactly that weight.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The weighted fermionic imaginary-time Green function
`G_{ij}(τ, τ') := -⟨T_τ c_i(τ) c_j†(τ')⟩_w`. -/
noncomputable def weightedFreeTwoPointFunction (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  - Common.normalizedWeightedDiagonal w (twoPointTimeOrderedProduct ε i j τ τ')

/-- For `τ' < τ`, time ordering leaves the annihilation field on the left. -/
theorem weightedFreeTwoPointFunction_of_gt (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode)
    {τ τ' : ℝ} (h : τ' < τ) :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      - Common.normalizedWeightedDiagonal w
          ((imaginaryTimeEvolve ε τ (annihilate i)).comp
            (imaginaryTimeEvolve ε τ' (create j))) := by
  rw [weightedFreeTwoPointFunction, twoPointTimeOrderedProduct_of_gt ε i j h]

/-- For `τ < τ'`, the fermionic exchange sign cancels the definition's outer minus sign. -/
theorem weightedFreeTwoPointFunction_of_lt (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode) {τ τ' : ℝ} (h : τ < τ') :
    weightedFreeTwoPointFunction ε w i j τ τ' =
      Common.normalizedWeightedDiagonal w
        ((imaginaryTimeEvolve ε τ' (create j)).comp
          (imaginaryTimeEvolve ε τ (annihilate i))) := by
  rw [weightedFreeTwoPointFunction, twoPointTimeOrderedProduct_of_lt ε i j h,
    Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one, neg_one_smul,
    Common.normalizedWeightedDiagonal, Common.weightedTrace]
  simp only [Common.matrixCoeff, LinearMap.neg_apply, Finsupp.neg_apply, mul_neg,
    Common.normalizedWeightedDiagonal, Common.weightedTrace, Finset.sum_neg_distrib, neg_div,
    neg_neg]

/-- At equal times, use the symmetric `θ(0) = 1/2` convention of the canonical two-point operator. -/
theorem weightedFreeTwoPointFunction_self_time (ε : Mode → ℝ) (w : Occupation Mode → ℂ)
    (i j : Mode) (τ : ℝ) :
    weightedFreeTwoPointFunction ε w i j τ τ =
      - Common.normalizedWeightedDiagonal w
          ((2⁻¹ : ℂ) • ((imaginaryTimeEvolve ε τ (annihilate i)).comp
              (imaginaryTimeEvolve ε τ (create j)) +
            (-1 : ℂ) •
              ((imaginaryTimeEvolve ε τ (create j)).comp
                (imaginaryTimeEvolve ε τ (annihilate i))))) := by
  rw [weightedFreeTwoPointFunction, twoPointTimeOrderedProduct_self_time,
    Common.Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]

/-- The free Gibbs two-point Green function, obtained by specializing the diagonal weight to the
free Boltzmann weight associated with the same one-particle energy `ε`. -/
noncomputable def freeGibbsGreenFunction (ε : Mode → ℝ) (β : ℝ)
    (i j : Mode) (τ τ' : ℝ) : ℂ :=
  weightedFreeTwoPointFunction ε (freeBoltzmannWeight ε β) i j τ τ'

end Fermionic
end SecondQuantization
