import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# Free-fermion coordinate expectation compatibility

The free Boltzmann weight and finite partition function are owned by `FreeBoltzmannCore`. This module
retains the temporary occupation-coordinate expectation and the bridges needed by the remaining
coordinate proofs. Its dependency direction is intentionally one-way: compatibility imports the
canonical free Gibbs density state, while the canonical state does not import this module.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

omit [DecidableEq Mode] [LinearOrder Mode] in
/-- The legacy total-weight presentation is the core free partition function. -/
theorem weightSum_freeBoltzmannWeight_eq_freePartitionFunction (ε : Mode → ℝ) (β : ℝ) :
    Common.weightSum (freeBoltzmannWeight ε β) = freePartitionFunction ε β := by
  rw [Common.weightSum, freePartitionFunction]

omit [DecidableEq Mode] [LinearOrder Mode] in
/-- The free finite fermion total weight is nonzero. -/
theorem weightSum_freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    Common.weightSum (freeBoltzmannWeight ε β) ≠ 0 := by
  rw [weightSum_freeBoltzmannWeight_eq_freePartitionFunction]
  exact freePartitionFunction_ne_zero ε β

/-- The temporary occupation-coordinate presentation of the free Gibbs expectation. -/
noncomputable def freeGibbsExpectation (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) : ℂ :=
  Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β) A

omit [LinearOrder Mode] in
theorem freeGibbsExpectation_smul (ε : Mode → ℝ) (β : ℝ) (c : ℂ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (c • A) = c * freeGibbsExpectation ε β A :=
  Common.normalizedWeightedDiagonal_smul c (freeBoltzmannWeight ε β) A

omit [LinearOrder Mode] in
theorem freeGibbsExpectation_neg (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (-A) = - freeGibbsExpectation ε β A := by
  rw [show (-A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) = (-1 : ℂ) • A from
    (neg_one_smul ℂ A).symm, freeGibbsExpectation_smul, neg_one_mul]

omit [LinearOrder Mode] in
theorem freeGibbsExpectation_operatorIntervalIntegral (ε : Mode → ℝ) (β : ℝ)
    (F : ℝ → FockSpace Mode →ₗ[ℂ] FockSpace Mode) (a b : ℝ)
    (hF : ∀ n : Occupation Mode, IntervalIntegrable
      (fun τ => Common.matrixCoeff (F τ) n n) MeasureTheory.volume a b) :
    freeGibbsExpectation ε β (Common.operatorIntervalIntegral F a b) =
      ∫ τ in a..b, freeGibbsExpectation ε β (F τ) :=
  Common.normalizedWeightedDiagonal_operatorIntervalIntegral (freeBoltzmannWeight ε β) F a b hF

/-- The free Gibbs two-point correlator. -/
noncomputable def freeGibbsGreenFunction (ε : Mode → ℝ) (β : ℝ) (i j : Mode) (τ τ' : ℝ) : ℂ :=
  weightedFreeTwoPointFunction ε (freeBoltzmannWeight ε β) i j τ τ'

omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in
/-- The fermionic and Common Boltzmann weights agree at `fermionEnergy`. -/
theorem freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    freeBoltzmannWeight ε β n = Common.boltzmannWeight (fermionEnergy ε) β n := by
  rw [freeBoltzmannWeight, Common.boltzmannWeight, fermionEnergy]
  push_cast
  ring_nf

omit [LinearOrder Mode] in
/-- The fermionic occupation-coordinate expectation agrees with the canonical finite Gibbs density
state. -/
theorem freeGibbsExpectation_eq_finiteGibbsExpectation (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β A = Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  rw [Common.finiteGibbsExpectation_eq_normalizedWeightedDiagonal]
  have hw : freeBoltzmannWeight ε β = Common.boltzmannWeight (fermionEnergy ε) β :=
    funext (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β)
  rw [freeGibbsExpectation, hw]

omit [LinearOrder Mode] in
/-- Temporary bridge from the canonical free Gibbs density state to the coordinate presentation. -/
theorem freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperator A) =
      freeGibbsExpectation ε β A := by
  rw [freeGibbsExpectation_eq_finiteGibbsExpectation]
  exact freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation ε β A

omit [LinearOrder Mode] in
/-- The canonical free Gibbs density-state expectation commutes with the finite algebraic operator
interval integral. This remains in the compatibility layer until the coordinate proof is replaced
by a direct transported-operator integral theorem. -/
theorem freeGibbsDensityOperator_expectation_operatorIntervalIntegral
    (ε : Mode → ℝ) (β : ℝ)
    (F : ℝ → FockSpace Mode →ₗ[ℂ] FockSpace Mode) (a b : ℝ)
    (hF : ∀ n : Occupation Mode, IntervalIntegrable
      (fun τ => Common.matrixCoeff (F τ) n n) MeasureTheory.volume a b) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (Common.operatorIntervalIntegral F a b)) =
      ∫ τ in a..b,
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator (F τ)) := by
  simp_rw [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation]
  exact freeGibbsExpectation_operatorIntervalIntegral ε β F a b hF

omit [LinearOrder Mode] in
theorem freeGibbsExpectation_finsetSum (ε : Mode → ℝ) (β : ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (∑ i ∈ s, F i) = ∑ i ∈ s, freeGibbsExpectation ε β (F i) := by
  simp_rw [freeGibbsExpectation_eq_finiteGibbsExpectation]
  exact map_sum (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) F s

end Fermionic
end SecondQuantization
