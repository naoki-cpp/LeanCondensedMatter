import LeanCondensedMatter.Analysis.Dyson.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

set_option linter.style.header false

/-!
# Bounds and convergence for generic bounded Dyson coefficients

This module proves the analytic estimates for the dimension-independent Dyson recursion from
`Analysis.Dyson.Basic`.  The interaction family is controlled by an explicit uniform norm bound on
a compact nonnegative time interval; no finite-dimensional realization or choice-based operator
bound is used here.
-/

namespace Dyson

open Set

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Continuous interaction families have continuous generic Dyson coefficients. -/
theorem continuous_coeff {V : ℝ → A} (hV : Continuous V) (n : ℕ) :
    Continuous (coeff V n) := by
  induction n with
  | zero =>
      change Continuous (fun _ : ℝ => (1 : A))
      fun_prop
  | succ n ih =>
      rw [continuous_iff_continuousAt]
      intro τ
      have hIntegrand : Continuous (fun σ : ℝ => V σ * coeff V n σ) := hV.mul ih
      have hPrimitive :
          HasDerivAt
            (fun t : ℝ => ∫ σ in (0 : ℝ)..t, V σ * coeff V n σ)
            (V τ * coeff V n τ) τ :=
        intervalIntegral.integral_hasDerivAt_right
          (hIntegrand.intervalIntegrable 0 τ)
          hIntegrand.stronglyMeasurable.stronglyMeasurableAtFilter
          hIntegrand.continuousAt
      change ContinuousAt
        (fun t : ℝ => -∫ σ in (0 : ℝ)..t, V σ * coeff V n σ) τ
      exact hPrimitive.continuousAt.neg

/-- Perturbatively weighted Dyson coefficients are continuous in time. -/
theorem continuous_term {V : ℝ → A} (hV : Continuous V) (lam : ℂ) (n : ℕ) :
    Continuous (fun τ => term V lam τ n) := by
  exact continuous_const.smul (continuous_coeff hV n)

/-- An explicit uniform bound on the interaction family implies the standard factorial estimate for
all generic Dyson coefficients on `[0, β]`. -/
theorem norm_coeff_le_of_bound (V : ℝ → A) {β M : ℝ}
    (hM : 0 ≤ M) (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖coeff V n τ‖ ≤ majorant M τ n := by
  induction n generalizing τ with
  | zero => simp
  | succ n ih =>
      rw [coeff_succ, norm_neg]
      calc
        ‖∫ σ in (0 : ℝ)..τ, V σ * coeff V n σ‖ ≤
            ∫ σ in (0 : ℝ)..τ, M * majorant M σ n := by
          apply intervalIntegral.norm_integral_le_of_norm_le hτ.1
          · refine Filter.Eventually.of_forall fun σ hσ => ?_
            have hσβ : σ ∈ Icc (0 : ℝ) β := ⟨hσ.1.le, hσ.2.trans hτ.2⟩
            calc
              ‖V σ * coeff V n σ‖ ≤ ‖V σ‖ * ‖coeff V n σ‖ := norm_mul_le _ _
              _ ≤ M * majorant M σ n :=
                mul_le_mul (hV σ hσβ) (ih hσβ) (norm_nonneg _) hM
          · have hcont : Continuous (fun σ : ℝ => M * majorant M σ n) := by
              unfold majorant
              fun_prop
            exact hcont.intervalIntegrable 0 τ
        _ = majorant M τ (n + 1) := integral_mul_majorant M τ n

/-- The weighted `n`th coefficient is controlled by the factorial majorant with interaction bound
`‖λ‖ M`. -/
theorem norm_term_le_of_bound (V : ℝ → A) {β M : ℝ}
    (hM : 0 ≤ M) (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖term V lam τ n‖ ≤ majorant (‖lam‖ * M) τ n := by
  calc
    ‖term V lam τ n‖ = ‖lam‖ ^ n * ‖coeff V n τ‖ := by
      rw [term, norm_smul, norm_pow]
    _ ≤ ‖lam‖ ^ n * majorant M τ n :=
      mul_le_mul_of_nonneg_left (norm_coeff_le_of_bound V hM hV n hτ)
        (pow_nonneg (norm_nonneg lam) n)
    _ = majorant (‖lam‖ * M) τ n := by
      simp only [majorant]
      ring_nf

/-- The weighted generic Dyson coefficients are summable at each time in a bounded interval. -/
theorem summable_term_of_bound (V : ℝ → A) {β M : ℝ}
    (hM : 0 ≤ M) (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    Summable (term V lam τ) := by
  have hnorm : Summable (fun n : ℕ => ‖term V lam τ n‖) :=
    (summable_majorant (‖lam‖ * M) τ).of_nonneg_of_le
      (fun n => norm_nonneg _) (fun n => norm_term_le_of_bound V hM hV lam n hτ)
  exact hnorm.of_norm

/-- The defining series has sum `evolution` whenever the interaction is uniformly bounded. -/
theorem hasSum_evolution_of_bound (V : ℝ → A) {β M : ℝ}
    (hM : 0 ≤ M) (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    HasSum (term V lam τ) (evolution V lam τ) := by
  exact (summable_term_of_bound V hM hV lam hτ).hasSum

/-- On a bounded nonnegative interval, the generic Dyson series converges uniformly in norm. -/
theorem hasSumUniformlyOn_evolution_of_bound (V : ℝ → A) {β M : ℝ}
    (hM : 0 ≤ M) (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) :
    HasSumUniformlyOn
      (fun n τ => term V lam τ n)
      (fun τ => evolution V lam τ)
      (Icc (0 : ℝ) β) := by
  have hWeighted : 0 ≤ ‖lam‖ * M := mul_nonneg (norm_nonneg lam) hM
  simpa only [evolution] using
    (HasSumUniformlyOn.of_norm_le_summable
      (f := fun n τ => term V lam τ n)
      (u := majorant (‖lam‖ * M) β)
      (summable_majorant (‖lam‖ * M) β)
      (fun n τ hτ =>
        (norm_term_le_of_bound V hM hV lam n hτ).trans
          (majorant_mono_time hWeighted hτ.1 hτ.2 n)))

end
end Dyson
