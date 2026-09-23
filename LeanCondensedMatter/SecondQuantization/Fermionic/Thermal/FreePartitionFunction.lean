import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# The free fermion partition function factorizes, and gives the Fermi–Dirac distribution

The closed-form free-fermion occupation number `⟨N_i⟩₀ = 1/(e^{βε_i}+1)` follows from the
mode-by-mode product factorization of the finite free partition function,

`Z₀(β) = Σₙ e^{-β E(n)} = ∏ᵢ (1 + e^{-βε_i})`.

Unlike the bosonic case (`Bosonic/Thermal/FreePartitionFunction.lean`), each fermionic mode's
occupation is `0` or `1`, so every sum is manifestly finite.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- The total free Boltzmann weight is nonzero. -/
theorem weightSum_freeBoltzmannWeight_ne_zero (ε : Mode → ℝ) (β : ℝ) :
    Common.weightSum (freeBoltzmannWeight ε β) ≠ 0 := by
  simpa [Common.weightSum, freePartitionFunction] using freePartitionFunction_ne_zero ε β

omit [LinearOrder Mode] [Fintype Mode] in
/-- The fermionic free Boltzmann weight is definitionally the Common weight at `fermionEnergy`. -/
theorem freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    freeBoltzmannWeight ε β n = Common.boltzmannWeight (fermionEnergy ε) β n :=
  rfl

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The free Boltzmann weight factorizes mode-by-mode**: `e^{-β E(n)} = ∏_{i ∈ n} e^{-βε_i}`,
since `E(n) = Σ_{i ∈ n} ε_i`. -/
theorem freeBoltzmannWeight_eq_prod (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    freeBoltzmannWeight ε β n = ∏ i ∈ n, Complex.exp (-(β : ℂ) * (ε i : ℂ)) := by
  rw [freeBoltzmannWeight, Common.boltzmannWeight, fermionEnergy, Finset.mul_sum]
  push_cast
  rw [Complex.exp_sum]

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The free Boltzmann weight, summed over all subsets of a fixed mode set `s`, factorizes** as
a product over `s`: `Σ_{t ⊆ s} e^{-β E(t)} = ∏_{i ∈ s} (1 + e^{-βε_i})`. The general-`s` form (not
just `s = univ`) is what lets `freeGibbsDensityOperator_expectation_numberOperator` below reuse
this for the mode-`i`-removed partial product `s = univ.erase i`. -/
theorem sum_freeBoltzmannWeight_powerset_eq_prod (ε : Mode → ℝ) (β : ℝ) (s : Finset Mode) :
    ∑ t ∈ s.powerset, freeBoltzmannWeight ε β t =
      ∏ j ∈ s, (1 + Complex.exp (-(β : ℂ) * (ε j : ℂ))) := by
  classical
  simp_rw [freeBoltzmannWeight_eq_prod]
  have h := Finset.prod_add (fun j => Complex.exp (-(β : ℂ) * (ε j : ℂ))) (fun _ => (1 : ℂ)) s
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun j _ => add_comm _ _


omit [LinearOrder Mode] in
/-- **The free partition function factorizes into a product over modes**:
`Z₀(β) = ∏ᵢ (1 + e^{-βε_i})`. -/
theorem freePartitionFunction_eq_prod (ε : Mode → ℝ) (β : ℝ) :
    freePartitionFunction ε β = ∏ i, (1 + Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
  classical
  rw [freePartitionFunction, ← Finset.powerset_univ]
  exact sum_freeBoltzmannWeight_powerset_eq_prod ε β Finset.univ

/-- **The closed-form Fermi–Dirac occupation number.** `⟨N_i⟩₀,β = 1/(e^{βε_i}+1)`. -/
theorem freeGibbsDensityOperator_expectation_numberOperator
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv (numberOperator i)) =
      1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) := by
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
  change Common.finiteGibbsExpectation (fermionEnergy ε) β
      ((create i).comp (annihilate i)) =
    1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
  have hC :
      Common.heisenbergEvolve (fermionEnergy ε) (-β) (create i) =
        Complex.exp (((ε i) * (-β) : ℝ) : ℂ) • create i := by
    have h := Common.heisenbergEvolve_eq_smul_of_carriesShift
      (fermionEnergy ε) (ε i) (-β) (create i)
      (carriesEnergyShift_create ε i)
    simpa [mul_comm] using h
  have hcomm :
      Common.exchangeCommutator Common.Statistics.fermion (create i) (annihilate i) =
        (1 : ℂ) • (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
    simpa [Common.exchangeCommutator, Common.Statistics.zetaInt_fermion] using
      (anticomm_create_annihilate (Mode := Mode) i i)
  have hne := one_sub_zetaInt_fermion_mul_exp_ne_zero (ε i) β
  have h := Common.finiteGibbsExpectation_comp_eq_div_of_exchangeCommutator
    (fermionEnergy ε) β (ε i) Common.Statistics.fermion (1 : ℂ)
    (create i) (annihilate i) hC hcomm hne
  simpa [Common.Statistics.zetaInt_fermion, mul_comm, add_comm] using h

end Fermionic
end SecondQuantization
