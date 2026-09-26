import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointEntropy

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
  purePointGibbsProbability (fermionEnergy ε) β n

omit [LinearOrder Mode] in
private theorem purePointPartitionFunction_fermionEnergy_eq_prod
    (ε : Mode → ℝ) (β : ℝ) :
    purePointPartitionFunction (fermionEnergy ε) β =
      ∏ i, (1 + Real.exp (-β * ε i)) := by
  apply Complex.ofReal_injective
  rw [← freePartitionFunction_eq_coe_purePointPartitionFunction,
    freePartitionFunction_eq_prod]
  push_cast [Complex.ofReal_exp]
  rfl

omit [LinearOrder Mode] in
private theorem log_purePointPartitionFunction_fermionEnergy_eq_sum
    (ε : Mode → ℝ) (β : ℝ) :
    Real.log (purePointPartitionFunction (fermionEnergy ε) β) =
      ∑ i, Real.log (1 + Real.exp (-β * ε i)) := by
  rw [purePointPartitionFunction_fermionEnergy_eq_prod]
  simpa using
    (Real.log_prod
      (s := (Finset.univ : Finset Mode))
      (f := fun i => 1 + Real.exp (-β * ε i))
      (fun i _ => ne_of_gt (by positivity)))

omit [LinearOrder Mode] [Fintype Mode] in
private theorem sum_purePointBoltzmannWeight_powerset_eq_prod
    (ε : Mode → ℝ) (β : ℝ) (s : Finset Mode) :
    ∑ t ∈ s.powerset, purePointBoltzmannWeight (fermionEnergy ε) β t =
      ∏ j ∈ s, (1 + Real.exp (-β * ε j)) := by
  simp_rw [purePointBoltzmannWeight, fermionEnergy, Finset.mul_sum, Real.exp_sum]
  have h := Finset.prod_add
    (fun j => Real.exp (-β * ε j)) (fun _ => (1 : ℝ)) s
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun j _ => add_comm _ _

omit [LinearOrder Mode] in
/-- The total probability of configurations containing mode `i` is its Fermi–Dirac occupation. -/
theorem sum_freeGibbsConfigurationProbability_filter_mem
    (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    ∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∈ ·),
        freeGibbsConfigurationProbability ε β n =
      fermiDiracOccupation ε β i := by
  let P : ℝ := ∏ j ∈ Finset.univ.erase i, (1 + Real.exp (-β * ε j))
  have hfilter_not :
      (Finset.univ : Finset (Occupation Mode)).filter (i ∉ ·) =
        (Finset.univ.erase i : Finset Mode).powerset := by
    ext t
    simp [Finset.mem_powerset, Finset.subset_erase]
  have hsum_not :
      ∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∉ ·),
          purePointBoltzmannWeight (fermionEnergy ε) β n = P := by
    rw [hfilter_not]
    exact sum_purePointBoltzmannWeight_powerset_eq_prod ε β (Finset.univ.erase i)
  have hZ :
      purePointPartitionFunction (fermionEnergy ε) β =
        (1 + Real.exp (-β * ε i)) * P := by
    rw [purePointPartitionFunction_fermionEnergy_eq_prod]
    change (∏ j, (1 + Real.exp (-β * ε j))) =
      (1 + Real.exp (-β * ε i)) *
        ∏ j ∈ Finset.univ.erase i, (1 + Real.exp (-β * ε j))
    exact (Finset.mul_prod_erase
      (Finset.univ : Finset Mode)
      (fun j => 1 + Real.exp (-β * ε j))
      (Finset.mem_univ i)).symm
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro j hj
    positivity
  have hnum :
      ∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∈ ·),
          purePointBoltzmannWeight (fermionEnergy ε) β n =
        Real.exp (-β * ε i) * P := by
    have hsplit :
        (∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∈ ·),
            purePointBoltzmannWeight (fermionEnergy ε) β n) +
          (∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∉ ·),
            purePointBoltzmannWeight (fermionEnergy ε) β n) =
          purePointPartitionFunction (fermionEnergy ε) β := by
      rw [purePointPartitionFunction, tsum_fintype]
      exact Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Occupation Mode)) (i ∈ ·)
        (purePointBoltzmannWeight (fermionEnergy ε) β)
    rw [hsum_not, hZ] at hsplit
    linear_combination hsplit
  simp_rw [freeGibbsConfigurationProbability, purePointGibbsProbability]
  rw [← Finset.mul_sum, hnum, hZ, fermiDiracOccupation]
  rw [show -β * ε i = -(β * ε i) by ring, Real.exp_neg]
  field_simp [hPpos.ne', Real.exp_ne_zero]

omit [LinearOrder Mode] in
/-- The mean free energy is the mode-energy sum weighted by Fermi–Dirac occupations. -/
theorem sum_freeGibbsConfigurationProbability_mul_fermionEnergy
    (ε : Mode → ℝ) (β : ℝ) :
    ∑ n : Occupation Mode,
        freeGibbsConfigurationProbability ε β n * fermionEnergy ε n =
      ∑ i, ε i * fermiDiracOccupation ε β i := by
  calc
    (∑ n : Occupation Mode,
        freeGibbsConfigurationProbability ε β n * fermionEnergy ε n) =
        ∑ n : Occupation Mode, ∑ i ∈ n,
          freeGibbsConfigurationProbability ε β n * ε i := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [fermionEnergy, Finset.mul_sum]
    _ = ∑ n : Occupation Mode, ∑ i : Mode,
          if i ∈ n then freeGibbsConfigurationProbability ε β n * ε i else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp
    _ = ∑ i : Mode, ∑ n : Occupation Mode,
          if i ∈ n then freeGibbsConfigurationProbability ε β n * ε i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Mode, ε i *
          (∑ n ∈ (Finset.univ : Finset (Occupation Mode)).filter (i ∈ ·),
            freeGibbsConfigurationProbability ε β n) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hni : i ∈ n <;> simp_all [mul_comm]
    _ = ∑ i, ε i * fermiDiracOccupation ε β i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sum_freeGibbsConfigurationProbability_filter_mem]

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
      PurePointGibbsEnergyIntegrable (fermionEnergy ε) β := by
    exact Summable.of_finite
  have hEntropy :
      (vonNeumannEntropy (freeGibbsDensityOperator ε β)).toReal =
        β * purePointGibbsEnergyExpectation (fermionEnergy ε) β +
          Real.log (purePointPartitionFunction (fermionEnergy ε) β) := by
    simpa [freeGibbsDensityOperator, finitePurePointGibbsDensityOperator] using
      (vonNeumannEntropy_purePointGibbsDensityOperator
        (Common.finiteHilbertBasis (Config := Occupation Mode))
        (fermionEnergy ε) β
        (purePointGibbsSummable_of_finite (fermionEnergy ε) β)
        hIntegrable).2
  have hEnergy :
      purePointGibbsEnergyExpectation (fermionEnergy ε) β =
        ∑ n : Occupation Mode,
          freeGibbsConfigurationProbability ε β n * fermionEnergy ε n := by
    rw [purePointGibbsEnergyExpectation, tsum_fintype]
    rfl
  rw [hEntropy, hEnergy,
    sum_freeGibbsConfigurationProbability_mul_fermionEnergy,
    log_purePointPartitionFunction_fermionEnergy_eq_sum]
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
