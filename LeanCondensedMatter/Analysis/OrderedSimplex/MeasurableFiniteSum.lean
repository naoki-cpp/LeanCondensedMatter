import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds

set_option linter.style.header false

/-!
# Finite sums of measurable ordered-simplex integrands

Global continuity is not needed to commute a finite sum with the recursively oriented
ordered-simplex integral.  Measurable local boundedness supplies exactly the recursive interval
integrability required by `intervalIntegral.integral_finsetSum` at every exposed coordinate.
-/

namespace intervalIntegral

open MeasureTheory

/-- Constant scalar multiplication preserves measurable local boundedness. -/
theorem MeasurableLocallyBounded.const_mul {n : ℕ}
    {f : (Fin n → ℝ) → ℂ} (hf : MeasurableLocallyBounded f) (c : ℂ) :
    MeasurableLocallyBounded (fun x => c * f x) := by
  refine ⟨measurable_const.mul hf.1, ?_⟩
  intro R hR
  obtain ⟨C, hC0, hC⟩ := hf.2 R hR
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC0, ?_⟩
  intro x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg c)

/-- A finite sum commutes with `orderedSimplexIntegral` when every summand is measurable and locally
bounded on finite-dimensional cubes. -/
theorem orderedSimplexIntegral_finsetSum_of_measurableLocallyBounded
    {ι : Type*} (s : Finset ι) :
    ∀ (n : ℕ) (β : ℝ) (f : ι → (Fin n → ℝ) → ℂ),
      (∀ i ∈ s, MeasurableLocallyBounded (f i)) →
      orderedSimplexIntegral n β (fun τ => ∑ i ∈ s, f i τ) =
        ∑ i ∈ s, orderedSimplexIntegral n β (f i)
  | 0, _β, f, _hf => by simp
  | n + 1, β, f, hf => by
      rw [orderedSimplexIntegral_succ]
      have heq : ∀ t : ℝ,
          orderedSimplexIntegral n t
              (fun rest => ∑ i ∈ s, f i (Fin.cons t rest)) =
            ∑ i ∈ s,
              orderedSimplexIntegral n t (fun rest => f i (Fin.cons t rest)) := by
        intro t
        exact orderedSimplexIntegral_finsetSum_of_measurableLocallyBounded s n t
          (fun i rest => f i (Fin.cons t rest))
          (fun i hi => (hf i hi).finCons t)
      simp_rw [heq]
      rw [intervalIntegral.integral_finsetSum]
      · exact Finset.sum_congr rfl fun i _ =>
          (orderedSimplexIntegral_succ n β (f i)).symm
      · intro i hi
        exact (hf i hi).intervalIntegrable_orderedSimplexIntegral_boundary β

end intervalIntegral
