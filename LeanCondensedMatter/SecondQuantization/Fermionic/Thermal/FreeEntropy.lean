import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.QuantumTheory.Gibbs.EigenbasisEntropy

set_option linter.style.header false

/-!
# Entropy of the finite free-fermion Gibbs state

The canonical free Gibbs density operator is the finite pure-point Gibbs state specialized to the
fermionic occupation basis. The generic pure-point Gibbs entropy identity gives
`S = β ⟨E⟩ + log Z`; mode factorization then reduces this to the sum of independent one-mode
binary entropies.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqFreeEntropy : DecidableEq Mode := Classical.decEq Mode

/-- The real Fermi–Dirac occupation of a single mode. -/
noncomputable def fermiDiracOccupation (ε : Mode → ℝ) (β : ℝ) (i : Mode) : ℝ :=
  (Real.exp (β * ε i) + 1)⁻¹

/-- The normalized probability of an occupation configuration in the free Gibbs state. -/
noncomputable def freeGibbsConfigurationProbability
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) : ℝ :=
  eigenbasisGibbsProbability (fermionEnergy ε) β n

omit [LinearOrder Mode] in
private theorem eigenbasisPartitionFunction_fermionEnergy_eq_prod
    (ε : Mode → ℝ) (β : ℝ) :
    eigenbasisPartitionFunction (fermionEnergy ε) β =
      ∏ i, (1 + Real.exp (-β * ε i)) := by
  apply Complex.ofReal_injective
  rw [← freePartitionFunction_eq_coe_eigenbasisPartitionFunction,
    freePartitionFunction_eq_prod]
  push_cast [Complex.ofReal_exp]
  rfl

omit [LinearOrder Mode] in
private theorem log_eigenbasisPartitionFunction_fermionEnergy_eq_sum
    (ε : Mode → ℝ) (β : ℝ) :
    Real.log (eigenbasisPartitionFunction (fermionEnergy ε) β) =
      ∑ i, Real.log (1 + Real.exp (-β * ε i)) := by
  rw [eigenbasisPartitionFunction_fermionEnergy_eq_prod]
  simpa using
    (Real.log_prod
      (s := (Finset.univ : Finset Mode))
      (f := fun i => 1 + Real.exp (-β * ε i))
      (fun i _ => ne_of_gt (by positivity)))

omit [LinearOrder Mode] in
/-- The total probability of configurations containing mode `i` is its Fermi–Dirac occupation. -/
theorem sum_freeGibbsConfigurationProbability_filter_mem
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    ∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∈ ·),
        freeGibbsConfigurationProbability ε β n =
      fermiDiracOccupation ε β i := by
  letI : LinearOrder Mode :=
    LinearOrder.lift' (Fintype.equivFin Mode) (Fintype.equivFin Mode).injective
  have h := freeGibbsDensityOperator_expectation_numberOperator ε β i
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    Common.finiteGibbsExpectation_eq_sum, numberOperator_eq_diagonalOperator] at h
  apply Complex.ofReal_injective
  push_cast
  simpa [Common.matrixCoeff_diagonalOperator, Finset.sum_filter, mul_ite,
    freeGibbsConfigurationProbability, fermiDiracOccupation] using h

omit [LinearOrder Mode] in
/-- The free-fermion Gibbs mean energy is the mode-energy sum weighted by Fermi–Dirac occupations. -/
theorem eigenbasisGibbsEnergyExpectation_fermionEnergy_eq_sum_fermiDirac
    (ε : Mode → ℝ) (β : ℝ) :
    eigenbasisGibbsEnergyExpectation (fermionEnergy ε) β =
      ∑ i, ε i * fermiDiracOccupation ε β i := by
  rw [eigenbasisGibbsEnergyExpectation, tsum_fintype]
  change
    (∑ n : Occupation Mode,
        freeGibbsConfigurationProbability ε β n * fermionEnergy ε n) =
      ∑ i, ε i * fermiDiracOccupation ε β i
  calc
    (∑ n : Occupation Mode,
        freeGibbsConfigurationProbability ε β n * fermionEnergy ε n) =
        ∑ n : Occupation Mode, ∑ i : Mode,
          if i ∈ n then freeGibbsConfigurationProbability ε β n * ε i else 0 := by
      simp [fermionEnergy, Finset.mul_sum]
    _ = ∑ i : Mode, ∑ n : Occupation Mode,
          if i ∈ n then freeGibbsConfigurationProbability ε β n * ε i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i, ε i * fermiDiracOccupation ε β i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      simp_rw [mul_comm (freeGibbsConfigurationProbability ε β _) (ε i)]
      rw [← Finset.mul_sum, sum_freeGibbsConfigurationProbability_filter_mem]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem fermiDiracOccupation_eq_exp_neg_div
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    fermiDiracOccupation ε β i =
      Real.exp (-β * ε i) / (1 + Real.exp (-β * ε i)) := by
  rw [fermiDiracOccupation, show -β * ε i = -(β * ε i) by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

omit [LinearOrder Mode] [Fintype Mode] in
private theorem one_sub_fermiDiracOccupation_eq_inv_one_add_exp_neg
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    1 - fermiDiracOccupation ε β i =
      (1 + Real.exp (-β * ε i))⁻¹ := by
  rw [fermiDiracOccupation, show -β * ε i = -(β * ε i) by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

omit [LinearOrder Mode] [Fintype Mode] in
private theorem binaryEntropy_fermiDiracOccupation
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    Real.negMulLog (fermiDiracOccupation ε β i) +
        Real.negMulLog (1 - fermiDiracOccupation ε β i) =
      (β * ε i) * fermiDiracOccupation ε β i +
        Real.log (1 + Real.exp (-β * ε i)) := by
  have hqpos : 0 < Real.exp (-β * ε i) := Real.exp_pos _
  have hdenpos : 0 < 1 + Real.exp (-β * ε i) := by positivity
  have hlogf :
      Real.log (fermiDiracOccupation ε β i) =
        -β * ε i - Real.log (1 + Real.exp (-β * ε i)) := by
    rw [fermiDiracOccupation_eq_exp_neg_div ε β i,
      Real.log_div hqpos.ne' hdenpos.ne', Real.log_exp]
  have hlog1mf :
      Real.log (1 - fermiDiracOccupation ε β i) =
        -Real.log (1 + Real.exp (-β * ε i)) := by
    rw [one_sub_fermiDiracOccupation_eq_inv_one_add_exp_neg ε β i,
      Real.log_inv]
  rw [Real.negMulLog, Real.negMulLog, hlogf, hlog1mf]
  ring

omit [LinearOrder Mode] in
/-- The finite free-fermion entropy is the sum of binary entropies of the Fermi–Dirac modes. -/
theorem vonNeumannEntropy_freeGibbsDensityOperator_toReal_eq_sum_fermiDirac
    (ε : Mode → ℝ) (β : ℝ) :
    (vonNeumannEntropy (freeGibbsDensityOperator ε β)).toReal =
      ∑ i, (Real.negMulLog (fermiDiracOccupation ε β i) +
        Real.negMulLog (1 - fermiDiracOccupation ε β i)) := by
  have hIntegrable :
      EigenbasisGibbsEnergyIntegrable (fermionEnergy ε) β := by
    exact Summable.of_finite
  have hEntropy :
      (vonNeumannEntropy (freeGibbsDensityOperator ε β)).toReal =
        β * eigenbasisGibbsEnergyExpectation (fermionEnergy ε) β +
          Real.log (eigenbasisPartitionFunction (fermionEnergy ε) β) := by
    simpa [freeGibbsDensityOperator] using
      (vonNeumannEntropy_eigenbasisGibbsDensityOperator
        (Common.finiteHilbertBasis (Config := Occupation Mode))
        (fermionEnergy ε) β
        (eigenbasisGibbsSummable_of_finite (fermionEnergy ε) β)
        hIntegrable).2
  rw [hEntropy,
    eigenbasisGibbsEnergyExpectation_fermionEnergy_eq_sum_fermiDirac,
    log_eigenbasisPartitionFunction_fermionEnergy_eq_sum]
  calc
    β * (∑ i, ε i * fermiDiracOccupation ε β i) +
        ∑ i, Real.log (1 + Real.exp (-β * ε i)) =
      ∑ i, ((β * ε i) * fermiDiracOccupation ε β i +
        Real.log (1 + Real.exp (-β * ε i))) := by
      rw [Finset.mul_sum, Finset.sum_add_distrib]
      ring_nf
    _ = ∑ i, (Real.negMulLog (fermiDiracOccupation ε β i) +
        Real.negMulLog (1 - fermiDiracOccupation ε β i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (binaryEntropy_fermiDiracOccupation ε β i).symm

end
end Fermionic
end SecondQuantization
