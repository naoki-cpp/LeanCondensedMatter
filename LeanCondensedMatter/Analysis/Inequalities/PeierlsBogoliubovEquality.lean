import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubov

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Equality cases for the Peierls–Bogoliubov inequality

This file isolates the strict scalar step needed to reverse the tangent-line proof of the
Peierls–Bogoliubov inequality for the Gibbs weight `x ↦ exp (-β x)`.
-/

/-- For nonzero `β`, the tangent line to `x ↦ exp (-β x)` at `x₀` lies strictly below the
exponential away from `x₀`. -/
theorem exp_tangent_strict (β x₀ x : ℝ) (hβ : β ≠ 0) (hx : x ≠ x₀) :
    (-β * Real.exp (-β * x₀)) * x +
        (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀) <
      Real.exp (-β * x) := by
  have harg_ne : -β * (x - x₀) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hβ) (sub_ne_zero.mpr hx)
  have hexp_ne : Real.exp (-β * (x - x₀)) ≠ 1 := by
    intro h
    apply harg_ne
    apply Real.exp_injective
    simpa using h
  have hlog := Real.log_lt_sub_one_of_pos
    (Real.exp_pos (-β * (x - x₀))) hexp_ne
  rw [Real.log_exp] at hlog
  have hexp : Real.exp (-β * x) =
      Real.exp (-β * x₀) * Real.exp (-β * (x - x₀)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hmul := mul_lt_mul_of_pos_left hlog (Real.exp_pos (-β * x₀))
  nlinarith

/-- For nonzero `β`, equality with the tangent line occurs exactly at the tangency point. -/
theorem exp_tangent_eq_iff (β x₀ x : ℝ) (hβ : β ≠ 0) :
    (-β * Real.exp (-β * x₀)) * x +
        (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀) =
      Real.exp (-β * x) ↔ x = x₀ := by
  constructor
  · intro heq
    by_contra hx
    exact (ne_of_lt (exp_tangent_strict β x₀ x hβ hx)) heq
  · rintro rfl
    ring
