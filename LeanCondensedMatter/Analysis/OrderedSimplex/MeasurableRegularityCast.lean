import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity

set_option linter.style.header false

namespace intervalIntegral

/-- Changing only the presentation of the finite coordinate count preserves measurable local
boundedness. -/
theorem MeasurableLocallyBounded.finCast {a b : ℕ} (h : a = b)
    {f : (Fin a → ℝ) → ℂ} (hf : MeasurableLocallyBounded f) :
    MeasurableLocallyBounded
      (fun τ : Fin b → ℝ => f (fun i => τ (Fin.cast h i))) := by
  subst b
  simpa using hf

end intervalIntegral
