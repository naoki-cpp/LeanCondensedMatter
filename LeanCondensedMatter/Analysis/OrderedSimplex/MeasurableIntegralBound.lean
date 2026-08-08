import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularityBounds

set_option linter.style.header false

/-!
# Integrability of measurable ordered-simplex primitives as the bound varies
-/

namespace intervalIntegral

open MeasureTheory Set

/-- For a measurable locally bounded integrand, its recursively oriented ordered-simplex integral
is interval integrable as a function of the outer bound on every finite interval. -/
theorem MeasurableLocallyBounded.intervalIntegrable_orderedSimplexIntegral_bound
    {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : MeasurableLocallyBounded f) (β : ℝ) :
    IntervalIntegrable (fun t : ℝ => orderedSimplexIntegral n t f) volume 0 β := by
  let H : ℝ → ℂ := fun t => orderedSimplexIntegral n t f
  have hMeas : Measurable H := by
    simpa [H] using measurable_orderedSimplexIntegral_bound f hf.1
  obtain ⟨C, hC0, hC⟩ := hf.2 |β| (abs_nonneg β)
  let D := C * |β| ^ n
  have hNorm : ∀ t ∈ Set.uIcc (0 : ℝ) β, ‖H t‖ ≤ D := by
    intro t ht
    have htAbs : |t| ≤ |β| := abs_le_abs_of_mem_uIcc_zero ht
    have hCube : ∀ x ∈ orderedSimplexTimeCube n |t|, ‖f x‖ ≤ C := by
      intro x hx
      exact hC x (orderedSimplexTimeCube_mono htAbs hx)
    have hi := norm_orderedSimplexIntegral_le_of_cube_bound n t f C hC0 hCube
    calc
      ‖H t‖ ≤ C * |t| ^ n := by simpa [H] using hi
      _ ≤ C * |β| ^ n := by gcongr
      _ = D := rfl
  have hIntOn : IntegrableOn H (Set.uIcc (0 : ℝ) β) := by
    exact MeasureTheory.IntegrableOn.of_bound
      isCompact_uIcc.measure_lt_top hMeas.aestronglyMeasurable D
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIcc hNorm)
  exact hIntOn.intervalIntegrable

end intervalIntegral
