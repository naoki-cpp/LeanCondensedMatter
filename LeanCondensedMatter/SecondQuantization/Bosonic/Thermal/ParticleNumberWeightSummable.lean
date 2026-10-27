import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BoltzmannWeightSummable
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonicalSectorDecomposition

set_option linter.style.header false

/-!
# Summability of particle-number-weighted bosonic Gibbs weights

For a fixed mode `j`, the series `Σ n, n(j) e^{-βE(n)}` converges under the same positivity
assumption as the partition sum. The proof replaces the `j`th one-mode geometric series by its
index-weighted version and applies the same finite-product `Finsupp` summation theorem.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqParticleNumberWeightSummable : DecidableEq Mode := Classical.decEq Mode

section FintypeMode

variable [Fintype Mode]

/-- The particle-number-weighted free Boltzmann series has its product closed form. -/
theorem hasSum_particleNumber_boltzmannWeight (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i) (j : Mode) :
    HasSum (fun n : Occupation Mode => (n j : ℝ) * boltzmannWeight ε β n)
      (Real.exp (-β * ε j) / (1 - Real.exp (-β * ε j)) ^ 2 *
        ∏ i ∈ Finset.univ.erase j, (1 - Real.exp (-β * ε i))⁻¹) := by
  set g' : Mode → ℕ → ℝ := fun i k =>
    if i = j then (k : ℝ) * oneModeBoltzmannWeight β (ε i) k
    else oneModeBoltzmannWeight β (ε i) k with hg'def
  set b' : Mode → ℝ := fun i =>
    if i = j then Real.exp (-β * ε j) / (1 - Real.exp (-β * ε j)) ^ 2
    else (1 - Real.exp (-β * ε i))⁻¹ with hb'def
  have hg' : ∀ i, HasSum (g' i) (b' i) := by
    intro i
    rw [hg'def, hb'def]
    dsimp only
    split_ifs with hi
    · subst j
      have hr : ‖Real.exp (-β * ε i)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
        linarith [hpos i]
      have h := hasSum_coe_mul_geometric_of_norm_lt_one hr
      exact HasSum.congr_fun h fun k => by
        unfold oneModeBoltzmannWeight
        rw [Real.exp_nat_mul]
    · exact hasSum_oneModeBoltzmannWeight (hpos i)
  have hnn' : ∀ i n, 0 ≤ g' i n := by
    intro i n
    rw [hg'def]
    dsimp only
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
    · exact Real.exp_nonneg _
  have H := Finsupp.hasSum_prod_nonneg g' b' hg' hnn'
  have hprod : ∀ i, i ∈ Finset.univ.erase j →
      b' i = (1 - Real.exp (-β * ε i))⁻¹ := fun i hi => by
    rw [hb'def]; simp [Finset.ne_of_mem_erase hi]
  rw [← Finset.mul_prod_erase Finset.univ b' (Finset.mem_univ j), hb'def] at H
  simp only [ite_true] at H
  rw [Finset.prod_congr rfl hprod] at H
  exact HasSum.congr_fun H fun n => by
    symm
    rw [← Finset.mul_prod_erase Finset.univ (fun i => g' i (n i)) (Finset.mem_univ j), hg'def]
    simp only [ite_true]
    have hrest : ∀ i, i ∈ Finset.univ.erase j →
        g' i (n i) = oneModeBoltzmannWeight β (ε i) (n i) := fun i hi => by
      rw [hg'def]; simp [Finset.ne_of_mem_erase hi]
    rw [Finset.prod_congr rfl hrest, mul_assoc, boltzmannWeight_eq_prod,
      Finset.mul_prod_erase Finset.univ (fun i => oneModeBoltzmannWeight β (ε i) (n i))
        (Finset.mem_univ j)]

end FintypeMode

/-- The particle-number-weighted free Boltzmann series is summable for any finite mode type. -/
theorem summable_particleNumber_boltzmannWeight [Finite Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i) (j : Mode) :
    Summable (fun n : Occupation Mode => (n j : ℝ) * boltzmannWeight ε β n) := by
  letI := Fintype.ofFinite Mode
  exact (hasSum_particleNumber_boltzmannWeight ε β hpos j).summable


/-- Finite-mode free bosons with strictly positive grand-canonical gaps have an
integrable total-number first moment. Hence the statistics-independent Common
grand-canonical mean is a genuine convergent spectral expectation. -/
theorem grandCanonicalParticleNumberIntegrable_of_finite [Finite Mode]
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ)) :
    Common.GrandCanonicalParticleNumberIntegrable
      (Config := Occupation Mode) ε β μ := by
  letI : Fintype Mode := Fintype.ofFinite Mode
  let ξ : Mode → ℝ := fun i => ε i - μ
  have hweighted : Summable (fun n : Occupation Mode =>
      (particleNumber n : ℝ) * boltzmannWeight ξ β n) := by
    have hterms : Summable (fun n : Occupation Mode =>
        ∑ i : Mode, (n i : ℝ) * boltzmannWeight ξ β n) :=
      summable_sum fun i (_ : i ∈ Finset.univ) =>
        summable_particleNumber_boltzmannWeight ξ β hpos i
    apply hterms.congr
    intro n
    rw [particleNumber_eq_sum_univ]
    push_cast
    rw [Finset.sum_mul]
  unfold Common.GrandCanonicalParticleNumberIntegrable
  have hscaled := hweighted.mul_left
    (Common.grandCanonicalPartitionFunction (Config := Occupation Mode) ε β μ)⁻¹
  apply hscaled.congr
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (QuantumTheory.eigenbasisGibbsProbability_nonneg
      (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β n)
    (Nat.cast_nonneg (particleNumber n)))]
  simp only [QuantumTheory.eigenbasisGibbsProbability,
    QuantumTheory.eigenbasisBoltzmannWeight, Common.grandCanonicalPartitionFunction,
    Common.grandCanonicalEnergy_eq_shifted, ξ, boltzmannWeight]
  have hshift : (fun i : Mode => ε i - μ) = (fun i : Mode => -μ + ε i) := by
    funext i
    ring
  simp only [freeEigenvalue]
  rw [hshift]
  ring

end
end Bosonic
end SecondQuantization
