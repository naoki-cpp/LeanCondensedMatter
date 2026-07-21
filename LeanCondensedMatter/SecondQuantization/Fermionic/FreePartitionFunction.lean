import LeanCondensedMatter.SecondQuantization.Fermionic.FreeBoltzmannWeight
import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedNumberOperator

set_option linter.style.header false

/-!
# The free fermion partition function factorizes, and gives the Fermi–Dirac distribution

Phase 9 follow-up (`notes/roadmaps/second-quantization.md`): closes the gap
`FreeBoltzmannWeight.lean`'s module docstring flags — the closed-form free-fermion occupation
number `⟨N_i⟩₀ = 1/(e^{βε_i}+1)` — via the mode-by-mode product factorization of the free
partition function,

`Z₀(β) = Σₙ e^{-β E(n)} = ∏ᵢ (1 + e^{-βε_i})`,

which needs no convergence theory: unlike the bosonic case (`Bosonic/FreePartitionFunction.lean`),
each fermionic mode's occupation is `0` or `1`, so every sum here is manifestly finite (a
`Finset.sum`/`Finset.prod` over `Fintype Mode`, no infinite series).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in
/-- **The free Boltzmann weight factorizes mode-by-mode**: `e^{-β E(n)} = ∏_{i ∈ n} e^{-βε_i}`,
since `E(n) = Σ_{i ∈ n} ε_i`. -/
theorem freeBoltzmannWeight_eq_prod (ε : Mode → ℝ) (β : ℝ) (n : FermionOccupation Mode) :
    freeBoltzmannWeight ε β n = ∏ i ∈ n, Complex.exp (-(β : ℂ) * (ε i : ℂ)) := by
  rw [freeBoltzmannWeight, Finset.mul_sum, Complex.exp_sum]

omit [DecidableEq Mode] [Fintype Mode] in
/-- **The free Boltzmann weight, summed over all subsets of a fixed mode set `s`, factorizes** as
a product over `s`: `Σ_{t ⊆ s} e^{-β E(t)} = ∏_{i ∈ s} (1 + e^{-βε_i})`. The general-`s` form (not
just `s = univ`) is what lets `freeGibbsExpectation_numberOperator` below reuse this for the
mode-`i`-removed partial product `s = univ.erase i`. -/
theorem sum_freeBoltzmannWeight_powerset_eq_prod (ε : Mode → ℝ) (β : ℝ) (s : Finset Mode) :
    ∑ t ∈ s.powerset, freeBoltzmannWeight ε β t =
      ∏ j ∈ s, (1 + Complex.exp (-(β : ℂ) * (ε j : ℂ))) := by
  simp_rw [freeBoltzmannWeight_eq_prod]
  have h := Finset.prod_add (fun j => Complex.exp (-(β : ℂ) * (ε j : ℂ))) (fun _ => (1 : ℂ)) s
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun j _ => add_comm _ _

omit [DecidableEq Mode] in
/-- **The free partition function factorizes into a product over modes**:
`Z₀(β) = ∏ᵢ (1 + e^{-βε_i})`. -/
theorem freePartitionFunction_eq_prod (ε : Mode → ℝ) (β : ℝ) :
    freePartitionFunction ε β = ∏ i, (1 + Complex.exp (-(β : ℂ) * (ε i : ℂ))) := by
  rw [freePartitionFunction, weightSum_eq_sum, ← Finset.powerset_univ]
  exact sum_freeBoltzmannWeight_powerset_eq_prod ε β Finset.univ

/-- **The closed-form Fermi–Dirac occupation number.** `⟨N_i⟩₀,β = 1/(e^{βε_i}+1)`. -/
theorem freeGibbsExpectation_numberOperator (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    freeGibbsExpectation ε β (numberOperator i) =
      1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) := by
  set f : Mode → ℂ := fun j => Complex.exp (-(β : ℂ) * (ε j : ℂ)) with hf
  set P : ℂ := ∏ j ∈ Finset.univ.erase i, (1 + f j) with hP
  have hfilter_not :
      (Finset.univ : Finset (FermionOccupation Mode)).filter (i ∉ ·) =
        (Finset.univ.erase i : Finset Mode).powerset := by
    ext t
    simp [Finset.mem_powerset, Finset.subset_erase]
  have hsum_not :
      ∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (i ∉ ·),
        freeBoltzmannWeight ε β n = P := by
    rw [hfilter_not]
    exact sum_freeBoltzmannWeight_powerset_eq_prod ε β _
  have hZ : freePartitionFunction ε β = (1 + f i) * P := by
    rw [freePartitionFunction_eq_prod, hP, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hPne : P ≠ 0 := by
    rw [← hsum_not]
    simp_rw [freeBoltzmannWeight_eq_ofReal]
    rw [← Complex.ofReal_sum]
    refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
    apply Finset.sum_pos (fun n _ => Real.exp_pos _)
    exact ⟨fermionVacuum, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [fermionVacuum]⟩⟩
  have hnum : weightedTrace (freeBoltzmannWeight ε β) (numberOperator i) = f i * P := by
    have hsplit :
        weightedTrace (freeBoltzmannWeight ε β) (numberOperator i) +
          ∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (i ∉ ·),
            freeBoltzmannWeight ε β n
          = freePartitionFunction ε β := by
      rw [weightedTrace_numberOperator, freePartitionFunction, weightSum_eq_sum]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ (i ∈ ·) (freeBoltzmannWeight ε β)
    rw [hsum_not, hZ] at hsplit
    linear_combination hsplit
  have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hfi : f i = (Complex.exp ((β : ℂ) * (ε i : ℂ)))⁻¹ := by
    change Complex.exp (-(β : ℂ) * (ε i : ℂ)) = (Complex.exp ((β : ℂ) * (ε i : ℂ)))⁻¹
    rw [show -(β : ℂ) * (ε i : ℂ) = -((β : ℂ) * (ε i : ℂ)) by ring, Complex.exp_neg]
  rw [freeGibbsExpectation, normalizedWeightedDiagonal_eq_div]
  change weightedTrace (freeBoltzmannWeight ε β) (numberOperator i) / freePartitionFunction ε β = _
  rw [hnum, hZ, hfi]
  field_simp

end SecondQuantization
