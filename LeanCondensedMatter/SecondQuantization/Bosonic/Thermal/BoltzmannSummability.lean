import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs
import LeanCondensedMatter.QuantumTheory.Gibbs.Boltzmann
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Finsupp.Basic

set_option linter.style.header false

/-!
# Boltzmann summability for the free boson Gibbs state

For finitely many bosonic modes with strictly positive one-particle energies at positive inverse
temperature, the existing occupation-level Boltzmann summability theorem supplies the generic
`QuantumTheory.EigenbasisGibbsSummable` hypothesis for `freeEigenvalue ε`.

This module is representation-independent: it also identifies the convergence-aware algebraic
`freeGibbsPartition` with the canonical pure-point partition function. Completed-space heat and
density operators consume these results downstream.
-/

namespace SecondQuantization
namespace Bosonic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- The algebraic occupation trace and the canonical pure-point partition sum are the same
for arbitrary bosonic mode types. This coordinate identity does not assert convergence. -/
theorem freeGibbsPartition_eq_coe_eigenbasisPartitionFunction
    (ε : Mode → ℝ) (β : ℝ) :
    freeGibbsPartition ε β =
      (eigenbasisPartitionFunction (freeEigenvalue ε) β : ℂ) := by
  unfold freeGibbsPartition Common.tsumTrace eigenbasisPartitionFunction
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [matrixCoeff_imaginaryTimeEvolveFree_self, eigenbasisBoltzmannWeight,
    Complex.ofReal_exp]

/-- Positive one-mode gaps and summable one-particle Boltzmann weights imply convergence
of the free-boson Gibbs partition sum over all finitely supported occupations, even for
infinitely many modes. -/
theorem eigenbasisGibbsSummable_freeEigenvalue_of_mode
    (ε : Mode → ℝ) (β : ℝ)
    (hpos : ∀ i, 0 < β * ε i)
    (hmode : EigenbasisGibbsSummable ε β) :
    EigenbasisGibbsSummable (freeEigenvalue ε) β := by
  classical
  let q : Mode → ℝ := fun i => Real.exp (-β * ε i)
  have hqpos (i : Mode) : 0 ≤ q i := Real.exp_nonneg _
  have hqlt (i : Mode) : q i < 1 := by
    change Real.exp (-β * ε i) < 1
    rw [Real.exp_lt_one_iff]
    linarith [hpos i]
  have hqnorm (i : Mode) : ‖q i‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hqpos i)]
    exact hqlt i
  have hqsum : Summable q := by
    change Summable (eigenbasisBoltzmannWeight ε β)
    exact eigenbasisBoltzmannWeight_summable ε β hmode
  have hsmall : ∀ᶠ i in Filter.cofinite, q i ≤ (1 / 2 : ℝ) :=
    hqsum.tendsto_cofinite_zero.eventually_le_const (by norm_num)
  have hratio : Summable (fun i : Mode => q i / (1 - q i)) := by
    apply (hqsum.mul_left (2 : ℝ)).of_norm_bounded_eventually
    filter_upwards [hsmall] with i hi
    have hden : 0 < 1 - q i := sub_pos.mpr (hqlt i)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hqpos i) hden.le)]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (hqpos i) (show 0 ≤ 1 - 2 * q i by linarith)]
  let g : Mode × ℕ → ℝ := fun p => if p.2 = 0 then 0 else q p.1 ^ p.2
  have hg_nonneg (p : Mode × ℕ) : 0 ≤ g p := by
    rcases p with ⟨i, k⟩
    simp only [g]
    split_ifs <;> positivity
  have hrow (i : Mode) : Summable (fun k : ℕ => g (i, k)) := by
    apply Summable.of_nonneg_of_le (fun k => hg_nonneg (i, k)) ?_
      (summable_geometric_of_norm_lt_one (hqnorm i))
    intro k
    by_cases hk : k = 0
    · simp [g, hk]
    · simp [g, hk]
  have hrow_sum (i : Mode) :
      (∑' k : ℕ, g (i, k)) = q i / (1 - q i) := by
    calc
      (∑' k : ℕ, g (i, k)) = g (i, 0) + ∑' k : ℕ, g (i, k + 1) :=
        (hrow i).tsum_eq_zero_add
      _ = ∑' k : ℕ, q i ^ (k + 1) := by simp [g]
      _ = (∑' k : ℕ, q i ^ k) * q i := by
        simp_rw [pow_succ]
        exact tsum_mul_right
      _ = (1 - q i)⁻¹ * q i := by
        rw [tsum_geometric_of_norm_lt_one (hqnorm i)]
      _ = q i / (1 - q i) := by ring
  have hg_sum : Summable g :=
    (summable_prod_of_nonneg hg_nonneg).2
      ⟨hrow, hratio.congr (fun i => (hrow_sum i).symm)⟩
  have hfinset : Summable
      (fun s : Finset (Mode × ℕ) => ∏ p ∈ s, g p) :=
    summable_finsetProd_of_summable_nonneg hg_nonneg hg_sum
  have hgraph_sum : Summable
      (fun n : Occupation Mode => ∏ p ∈ n.graph, g p) := by
    simpa only [Function.comp_def] using
      (hfinset.comp_injective (Finsupp.graph_injective Mode ℕ))
  have hgraph_prod (n : Occupation Mode) :
      (∏ p ∈ n.graph, g p) = ∏ i ∈ n.support, q i ^ n i := by
    simp only [Finsupp.graph, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro i hi
    change (if n i = 0 then (0 : ℝ) else q i ^ n i) = q i ^ n i
    simp [Finsupp.mem_support_iff.mp hi]
  have hweight (n : Occupation Mode) :
      eigenbasisBoltzmannWeight (freeEigenvalue ε) β n =
        ∏ p ∈ n.graph, g p := by
    rw [hgraph_prod]
    change Real.exp (-β * freeEigenvalue ε n) = _
    calc
      Real.exp (-β * freeEigenvalue ε n) =
          Real.exp (∑ i ∈ n.support, (n i : ℝ) * (-β * ε i)) := by
        congr 1
        simp only [freeEigenvalue_eq_finsupp_sum, Finsupp.sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∏ i ∈ n.support, q i ^ n i := by
        rw [Real.exp_sum]
        apply Finset.prod_congr rfl
        intro i hi
        simp only [q, Real.exp_nat_mul]
  unfold EigenbasisGibbsSummable
  exact hgraph_sum.congr fun n => by
    rw [← hweight n]
    exact (abs_of_nonneg
      (eigenbasisBoltzmannWeight_nonneg (freeEigenvalue ε) β n)).symm

variable [Finite Mode]

/-- Positive one-particle energies make the free occupation Boltzmann weights absolutely summable. -/
theorem eigenbasisGibbsSummable_freeEigenvalue
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 < β) (hε : ∀ i, 0 < ε i) :
    EigenbasisGibbsSummable (freeEigenvalue ε) β := by
  letI := Fintype.ofFinite Mode
  unfold EigenbasisGibbsSummable
  have hsum := summable_boltzmannWeight ε β (fun i => mul_pos hβ (hε i))
  exact hsum.congr fun n => by
    simp [boltzmannWeight, eigenbasisBoltzmannWeight, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]

end
end Bosonic
end SecondQuantization
