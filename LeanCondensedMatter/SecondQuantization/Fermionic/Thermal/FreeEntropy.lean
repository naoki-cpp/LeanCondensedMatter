import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.QuantumTheory.Entropy.Finite
import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Entropy of the finite free-fermion Gibbs state

The canonical free Gibbs density operator is diagonal in the occupation basis. Its von Neumann
entropy therefore reduces to the Shannon entropy of the normalized occupation weights, which
factorizes into the sum of independent one-mode binary entropies.
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
@[simp]
theorem freeGibbsDensityOperator_apply_basis_probability
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    (freeGibbsDensityOperator ε β).op (Common.finiteHilbertBasisState n) =
      (freeGibbsConfigurationProbability ε β n : ℂ) •
        Common.finiteHilbertBasisState n := by
  simpa [freeGibbsConfigurationProbability] using
    freeGibbsDensityOperator_apply_basis ε β n

omit [LinearOrder Mode] in
theorem freeGibbsConfigurationProbability_pos
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    0 < freeGibbsConfigurationProbability ε β n := by
  rw [freeGibbsConfigurationProbability, purePointGibbsProbability]
  exact mul_pos
    (inv_pos.mpr (purePointPartitionFunction_pos (fermionEnergy ε) β
      (purePointGibbsSummable_of_finite (fermionEnergy ε) β)))
    (purePointBoltzmannWeight_pos (fermionEnergy ε) β n)

omit [LinearOrder Mode] in
theorem sum_freeGibbsConfigurationProbability_eq_one (ε : Mode → ℝ) (β : ℝ) :
    ∑ n : Occupation Mode, freeGibbsConfigurationProbability ε β n = 1 := by
  have h := hasSum_purePointGibbsProbability (fermionEnergy ε) β
    (purePointGibbsSummable_of_finite (fermionEnergy ε) β)
  simpa [freeGibbsConfigurationProbability, tsum_fintype] using h.tsum_eq

omit [LinearOrder Mode] in
private theorem purePointPartitionFunction_fermionEnergy_eq_prod
    (ε : Mode → ℝ) (β : ℝ) :
    purePointPartitionFunction (fermionEnergy ε) β =
      ∏ i, (1 + Real.exp (-β * ε i)) := by
  rw [purePointPartitionFunction, tsum_fintype, ← Finset.powerset_univ]
  simp_rw [purePointBoltzmannWeight, fermionEnergy, Finset.mul_sum, Real.exp_sum]
  have h := Finset.prod_add
    (fun i => Real.exp (-β * ε i)) (fun _ => (1 : ℝ))
    (Finset.univ : Finset Mode)
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun i _ => add_comm _ _

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

omit [LinearOrder Mode] in
theorem sum_negMulLog_freeGibbsConfigurationProbability
    (ε : Mode → ℝ) (β : ℝ) :
    ∑ n : Occupation Mode,
        Real.negMulLog (freeGibbsConfigurationProbability ε β n) =
      β * (∑ n : Occupation Mode,
        freeGibbsConfigurationProbability ε β n * fermionEnergy ε n) +
        Real.log (purePointPartitionFunction (fermionEnergy ε) β) := by
  let Z := purePointPartitionFunction (fermionEnergy ε) β
  have hZpos : 0 < Z := purePointPartitionFunction_pos (fermionEnergy ε) β
    (purePointGibbsSummable_of_finite (fermionEnergy ε) β)
  have hlog (n : Occupation Mode) :
      Real.log (freeGibbsConfigurationProbability ε β n) =
        -β * fermionEnergy ε n - Real.log Z := by
    rw [freeGibbsConfigurationProbability, purePointGibbsProbability,
      purePointBoltzmannWeight,
      Real.log_mul (inv_ne_zero hZpos.ne') (ne_of_gt (Real.exp_pos _)),
      Real.log_inv, Real.log_exp]
    ring
  have hterm (n : Occupation Mode) :
      Real.negMulLog (freeGibbsConfigurationProbability ε β n) =
        β * (freeGibbsConfigurationProbability ε β n * fermionEnergy ε n) +
          Real.log Z * freeGibbsConfigurationProbability ε β n := by
    rw [Real.negMulLog, hlog n]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_freeGibbsConfigurationProbability_eq_one, mul_one]

omit [LinearOrder Mode] in
theorem vonNeumannEntropy_freeGibbsDensityOperator_toReal_eq_sum_configuration
    (ε : Mode → ℝ) (β : ℝ) :
    (vonNeumannEntropy (freeGibbsDensityOperator ε β)).toReal =
      ∑ n : Occupation Mode,
        Real.negMulLog (freeGibbsConfigurationProbability ε β n) := by
  let ρ := freeGibbsDensityOperator ε β
  let b := Common.finiteHilbertBasis (Config := Occupation Mode)
  let w := freeGibbsConfigurationProbability ε β
  let hs := ρ.entropyOp_hasSummableRealEigenvalues
  have happly (n : Occupation Mode) :
      ρ.op (b n) = (w n : ℂ) • b n := by
    simpa [ρ, b, w] using freeGibbsDensityOperator_apply_basis_probability ε β n
  have hw_nonneg (n : Occupation Mode) : 0 ≤ w n :=
    (freeGibbsConfigurationProbability_pos ε β n).le
  have hw_le_one (n : Occupation Mode) : w n ≤ 1 :=
    ρ.diagonal_weight_le_one b w happly hw_nonneg n
  have htrace := entropyOpSpectralTraceClass_trace_eq_tsum_diagonal
    ρ b w happly hs
  have htrace_nonneg : 0 ≤ (entropyOpSpectralTraceClass ρ hs).trace := by
    rw [htrace]
    exact tsum_nonneg fun n => Real.negMulLog_nonneg (hw_nonneg n) (hw_le_one n)
  rw [vonNeumannEntropy_eq_ofReal_entropyOp_trace ρ hs,
    ENNReal.toReal_ofReal htrace_nonneg, htrace, tsum_fintype]

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
  field_simp [Real.exp_ne_zero] <;> ring

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
  rw [vonNeumannEntropy_freeGibbsDensityOperator_toReal_eq_sum_configuration,
    sum_negMulLog_freeGibbsConfigurationProbability,
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
