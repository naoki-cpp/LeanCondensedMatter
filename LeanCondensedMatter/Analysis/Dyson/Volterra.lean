import LeanCondensedMatter.Analysis.Dyson.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option linter.style.header false

/-!
# Generic Volterra equation for bounded Dyson evolutions

This module exchanges the generic Dyson series with its Bochner interval integral and proves the
interaction-picture Volterra equation. The only quantitative input is an explicit uniform bound
for the interaction family on a compact nonnegative time interval.
-/

namespace Dyson

open Set

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The `n`th term in the Volterra integrand, including the external coupling. -/
noncomputable def integrand (V : ℝ → A) (lam : ℂ) (n : ℕ) (σ : ℝ) : A :=
  lam • (V σ * term V lam σ n)

/-- A constant-in-time summable majorant for the Volterra integrand on `[0, β]`. -/
noncomputable def integrandMajorant (M β : ℝ) (lam : ℂ) (n : ℕ) : ℝ :=
  (‖lam‖ * M) * majorant (‖lam‖ * M) β n

/-- Every generic Volterra-integrand term is continuous for a continuous interaction family. -/
theorem continuous_integrand {V : ℝ → A} (hV : Continuous V) (lam : ℂ) (n : ℕ) :
    Continuous (integrand V lam n) := by
  change Continuous (fun σ => lam • (V σ * term V lam σ n))
  exact continuous_const.smul (hV.mul (continuous_term hV lam n))

/-- Left multiplication by the interaction and scalar multiplication carry the Dyson sum to the
pointwise Volterra integrand. -/
theorem hasSum_integrand_of_bound (V : ℝ → A) {β M σ : ℝ}
    (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M)
    (hσ : σ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (fun n => integrand V lam n σ)
      (lam • (V σ * evolution V lam σ)) := by
  have hmul := (hasSum_evolution_of_bound V hOne hM hV lam hσ).mul_left (V σ)
  simpa only [integrand] using hmul.const_smul lam

/-- The generic Volterra-integrand majorant is summable. -/
theorem summable_integrandMajorant (M β : ℝ) (lam : ℂ) :
    Summable (integrandMajorant M β lam) := by
  exact (summable_majorant (‖lam‖ * M) β).mul_left (‖lam‖ * M)

omit [CompleteSpace A] in
/-- Uniform pointwise norm control of every generic Volterra-integrand term on `[0, β]`. -/
theorem norm_integrand_le_of_bound (V : ℝ → A) {β M σ : ℝ}
    (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M)
    (hσ : σ ∈ Icc (0 : ℝ) β) (lam : ℂ) (n : ℕ) :
    ‖integrand V lam n σ‖ ≤ integrandMajorant M β lam n := by
  have hweighted : 0 ≤ ‖lam‖ * M := mul_nonneg (norm_nonneg lam) hM
  have hterm : ‖term V lam σ n‖ ≤ majorant (‖lam‖ * M) β n :=
    (norm_term_le_of_bound V hOne hM hV lam n hσ).trans
      (majorant_mono_time hweighted hσ.1 hσ.2 n)
  calc
    ‖integrand V lam n σ‖ = ‖lam‖ * ‖V σ * term V lam σ n‖ := by
      rw [integrand, norm_smul]
    _ ≤ ‖lam‖ * (‖V σ‖ * ‖term V lam σ n‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg lam)
    _ ≤ ‖lam‖ * (M * majorant (‖lam‖ * M) β n) := by
      gcongr
      exact hV σ hσ
    _ = integrandMajorant M β lam n := by
      rw [integrandMajorant]
      ring

/-- The generic Volterra integrand series may be exchanged with the Bochner interval integral. -/
theorem hasSum_intervalIntegral_integrand_of_bound {V : ℝ → A} (hVcont : Continuous V)
    {β M τ : ℝ} (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum
      (fun n => ∫ σ in (0 : ℝ)..τ, integrand V lam n σ)
      (∫ σ in (0 : ℝ)..τ, lam • (V σ * evolution V lam σ)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n _ => integrandMajorant M β lam n)
  · intro n
    exact (continuous_integrand hVcont lam n).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun σ hσ => by
      have hσ' : σ ∈ Icc (0 : ℝ) τ := by
        simpa [uIcc_of_le hτ.1] using (uIoc_subset_uIcc hσ)
      exact norm_integrand_le_of_bound V hOne hM hV
        ⟨hσ'.1, hσ'.2.trans hτ.2⟩ lam n
  · exact Filter.Eventually.of_forall fun _ _ => summable_integrandMajorant M β lam
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun σ hσ => by
      have hσ' : σ ∈ Icc (0 : ℝ) τ := by
        simpa [uIcc_of_le hτ.1] using (uIoc_subset_uIcc hσ)
      exact hasSum_integrand_of_bound V hOne hM hV
        ⟨hσ'.1, hσ'.2.trans hτ.2⟩ lam

omit [CompleteSpace A] in
/-- Integrating the `n`th generic Volterra term gives the negative `(n+1)`st Dyson term. -/
theorem intervalIntegral_integrand (V : ℝ → A) (τ : ℝ) (lam : ℂ) (n : ℕ) :
    (∫ σ in (0 : ℝ)..τ, integrand V lam n σ) = - term V lam τ (n + 1) := by
  rw [term, coeff_succ, smul_neg, neg_neg]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro σ _
  simp [integrand, term, pow_succ', smul_smul]

/-- The positive-order generic Dyson tail sums to the negative Volterra integral. -/
theorem hasSum_tail_of_bound {V : ℝ → A} (hVcont : Continuous V)
    {β M τ : ℝ} (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    HasSum (fun n => term V lam τ (n + 1))
      (- ∫ σ in (0 : ℝ)..τ, lam • (V σ * evolution V lam σ)) := by
  simpa only [neg_neg] using
    (HasSum.congr_fun
      (hasSum_intervalIntegral_integrand_of_bound hVcont hOne hM hV hτ lam)
      (fun n => (intervalIntegral_integrand V τ lam n).symm)).neg

/-- The generic Dyson evolution solves the interaction-picture Volterra equation. -/
theorem evolution_eq_one_sub_integral_of_bound {V : ℝ → A} (hVcont : Continuous V)
    {β M τ : ℝ} (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ t ∈ Icc (0 : ℝ) β, ‖V t‖ ≤ M)
    (hτ : τ ∈ Icc (0 : ℝ) β) (lam : ℂ) :
    evolution V lam τ = 1 - lam • ∫ σ in (0 : ℝ)..τ, V σ * evolution V lam σ := by
  have hfull := hasSum_evolution_of_bound V hOne hM hV lam hτ
  have hdecomp : HasSum (term V lam τ)
      (term V lam τ 0 +
        (- ∫ σ in (0 : ℝ)..τ, lam • (V σ * evolution V lam σ))) :=
    (hasSum_tail_of_bound hVcont hOne hM hV hτ lam).zero_add
  have heq := hfull.unique hdecomp
  simpa [term, sub_eq_add_neg, intervalIntegral.integral_smul] using heq

end
end Dyson
