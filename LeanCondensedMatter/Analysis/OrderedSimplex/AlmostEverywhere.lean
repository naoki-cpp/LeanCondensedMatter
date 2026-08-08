import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Almost-everywhere congruence for ordered-simplex integrals

The recursive ordered-simplex integral is insensitive to finitely many forbidden values in each
time coordinate. This packages the null-diagonal argument needed when a finite-time integrand is
only covariant for injective coordinate assignments.
-/

namespace intervalIntegral

open MeasureTheory

private theorem finCons_injective_of_injective_avoids
    {n : ℕ} (t : ℝ) (rest : Fin n → ℝ)
    (hrest : Function.Injective rest) (ht : ∀ i, rest i ≠ t) :
    Function.Injective (Fin.cons t rest) := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ b =>
          exfalso
          exact ht b (by simpa using hab.symm)
  | succ a =>
      induction b using Fin.cases with
      | zero =>
          exfalso
          exact ht a (by simpa using hab)
      | succ b =>
          exact congrArg Fin.succ (hrest (by simpa using hab))

private theorem orderedSimplexIntegral_congr_avoiding_finset :
    ∀ (n : ℕ) (β : ℝ) (f g : (Fin n → ℝ) → ℂ) (forbidden : Finset ℝ),
      (∀ τ, Function.Injective τ → (∀ i, τ i ∉ forbidden) → f τ = g τ) →
      orderedSimplexIntegral n β f = orderedSimplexIntegral n β g
  | 0, β, f, g, forbidden, h => by
      exact h Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | n + 1, β, f, g, forbidden, h => by
      rw [orderedSimplexIntegral_succ, orderedSimplexIntegral_succ]
      apply intervalIntegral.integral_congr_ae
      have havoid : ∀ᵐ t : ℝ ∂volume, t ∉ forbidden := by
        simpa using ((measure_eq_zero_iff_ae_notMem).1
          (Finset.measure_zero forbidden volume))
      filter_upwards [havoid] with t ht
      intro _ht
      apply orderedSimplexIntegral_congr_avoiding_finset n t
        (fun rest => f (Fin.cons t rest))
        (fun rest => g (Fin.cons t rest)) (insert t forbidden)
      intro rest hrest hforbidden
      apply h (Fin.cons t rest)
      · apply finCons_injective_of_injective_avoids t rest hrest
        intro i
        exact (Finset.not_mem_insert.mp (hforbidden i)).1
      · intro i
        induction i using Fin.cases with
        | zero => simpa using ht
        | succ i => exact (Finset.not_mem_insert.mp (hforbidden i)).2

/-- Two ordered-simplex integrands have the same integral when they agree on injective time
assignments. The complement consists only of recursively encountered coordinate-collision
hyperplanes and is discarded by one-dimensional a.e. congruence at each integration level. -/
theorem orderedSimplexIntegral_congr_of_injective
    {n : ℕ} {β : ℝ} {f g : (Fin n → ℝ) → ℂ}
    (h : ∀ τ, Function.Injective τ → f τ = g τ) :
    orderedSimplexIntegral n β f = orderedSimplexIntegral n β g := by
  exact orderedSimplexIntegral_congr_avoiding_finset n β f g ∅
    (fun τ hτ _ => h τ hτ)

end intervalIntegral
