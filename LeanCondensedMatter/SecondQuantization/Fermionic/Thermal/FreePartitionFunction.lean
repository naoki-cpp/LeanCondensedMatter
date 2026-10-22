import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator

set_option linter.style.header false

/-!
# Factorization of the finite free-fermion partition function

`Z₀(β) = Σₙ e^{-β E(n)} = ∏ᵢ (1 + e^{-βε_i})`.

Each fermionic mode has occupation `0` or `1`, so the configuration sum is finite.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The free Boltzmann weight factorizes mode-by-mode**: `e^{-β E(n)} = ∏_{i ∈ n} e^{-βε_i}`,
since `E(n) = Σ_{i ∈ n} ε_i`. -/
theorem freeBoltzmannWeight_eq_prod (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    freeBoltzmannWeight ε β n = ∏ i ∈ n, Complex.exp (-(β : ℂ) * (ε i : ℂ)) := by
  rw [freeBoltzmannWeight, Common.boltzmannWeight, fermionEnergy_eq_sum, Finset.mul_sum]
  push_cast
  rw [Complex.exp_sum]

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The free Boltzmann weight, summed over all subsets of a fixed mode set `s`, factorizes** as
a product over `s`: `Σ_{t ⊆ s} e^{-β E(t)} = ∏_{i ∈ s} (1 + e^{-βε_i})`. The general-`s` form
keeps the mode-set factorization available independently of the `s = univ` partition function. -/
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

end Fermionic
end SecondQuantization
