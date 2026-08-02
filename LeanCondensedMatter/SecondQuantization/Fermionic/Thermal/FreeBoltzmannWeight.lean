import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# The free Boltzmann weight, and the genuine free thermal Green function

The fermionic free thermal formulas retain their occupation-basis presentation during the E3
migration, while `freeGibbsExpectation_eq_finiteGibbsExpectation` identifies that presentation with
the canonical finite Gibbs density state. The fermionic definition itself is removed in the
following E4 package after all physics-facing callers have moved.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The free Boltzmann weight `e^{-βE(n)}` for `E(n) = Σᵢ∈n ε(i)`. -/
noncomputable def freeBoltzmannWeight (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℂ :=
  Complex.exp (-(β : ℂ) * ∑ i ∈ n, (ε i : ℂ))

omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in
/-- The free Boltzmann weight is a cast of a positive real number. -/
theorem freeBoltzmannWeight_eq_ofReal (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    freeBoltzmannWeight ε β n = ((Real.exp (-β * ∑ i ∈ n, ε i) : ℝ) : ℂ) := by
  rw [freeBoltzmannWeight,
    show -(β : ℂ) * ∑ i ∈ n, (ε i : ℂ) = ((-β * ∑ i ∈ n, ε i : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_exp]

omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in
theorem freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    freeBoltzmannWeight ε β n ≠ 0 :=
  Complex.exp_ne_zero _

omit [DecidableEq Mode] [LinearOrder Mode] in
/-- The free finite fermion partition function is nonzero. -/
theorem weightSum_freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    Common.weightSum (freeBoltzmannWeight ε β) ≠ 0 := by
  rw [Common.weightSum]
  simp_rw [freeBoltzmannWeight_eq_ofReal]
  rw [← Complex.ofReal_sum]
  refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
  exact Finset.sum_pos (fun n _ => Real.exp_pos _) Finset.univ_nonempty

/-- The free partition function `Z₀(β)`. -/
noncomputable def freePartitionFunction (ε : Mode → ℝ) (β : ℝ) : ℂ :=
  Common.weightSum (freeBoltzmannWeight ε β)

omit [DecidableEq Mode] [LinearOrder Mode] in
theorem freePartitionFunction_ne_zero (ε : Mode → ℝ) (β : ℝ) : freePartitionFunction ε β ≠ 0 :=
  weightSum_freeBoltzmannWeight_ne_zero ε β

/-- The occupation-coordinate presentation of the free Gibbs expectation. It is identified with the
canonical density-state expectation below and will be removed in E4. -/
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
state. This migration theorem is removed together with `freeGibbsExpectation` in E4. -/
theorem freeGibbsExpectation_eq_finiteGibbsExpectation (ε : Mode → ℝ) (β : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β A = Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  rw [Common.finiteGibbsExpectation_eq_normalizedWeightedDiagonal]
  have hw : freeBoltzmannWeight ε β = Common.boltzmannWeight (fermionEnergy ε) β :=
    funext (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β)
  rw [freeGibbsExpectation, hw]

omit [LinearOrder Mode] in
theorem freeGibbsExpectation_finsetSum (ε : Mode → ℝ) (β : ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (∑ i ∈ s, F i) = ∑ i ∈ s, freeGibbsExpectation ε β (F i) := by
  simp_rw [freeGibbsExpectation_eq_finiteGibbsExpectation]
  exact map_sum (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) F s

end Fermionic
end SecondQuantization
