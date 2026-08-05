import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Continuity helpers for ordered-simplex recursion

Small reusable facts for adjoining the current outer integration variable to a finite time tuple,
or for lifting an integrand across an extra parameter that it does not use.
-/

namespace intervalIntegral

/-- Prepending a varying real coordinate to a finite tuple preserves continuity after composition. -/
theorem continuous_finCons_comp {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    {f : (Fin (n + 1) → ℝ) → Y} (hf : Continuous f) :
    Continuous (Function.uncurry
      (fun t : ℝ => fun rest : Fin n → ℝ => f (Fin.cons t rest))) := by
  exact hf.comp (Continuous.finCons continuous_fst continuous_snd)

/-- For a jointly continuous parameterized integrand, adjoining the current outer integration
variable as its first finite coordinate preserves joint continuity. -/
theorem continuous_uncurry_finCons {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {f : X → (Fin (n + 1) → ℝ) → Y}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry
      (fun y : X × ℝ => fun rest : Fin n → ℝ => f y.1 (Fin.cons y.2 rest))) := by
  have hcons : Continuous
      (fun z : (X × ℝ) × (Fin n → ℝ) =>
        (Fin.cons z.1.2 z.2 : Fin (n + 1) → ℝ)) :=
    Continuous.finCons (continuous_snd.comp continuous_fst) continuous_snd
  exact hf.comp ((continuous_fst.comp continuous_fst).prodMk hcons)

/-- A jointly continuous parameterized integrand remains jointly continuous after adding an extra
real parameter that the integrand ignores. -/
theorem continuous_uncurry_fst {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {f : X → (Fin n → ℝ) → Y}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry
      (fun y : X × ℝ => fun times : Fin n → ℝ => f y.1 times)) := by
  exact hf.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)

end intervalIntegral
