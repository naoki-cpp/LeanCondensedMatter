import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubov

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Equality cases for the Peierls–Bogoliubov inequality

This file isolates the strict scalar and finite weighted-sum steps needed to reverse the
tangent-line proof of the Peierls–Bogoliubov inequality for the Gibbs weight
`x ↦ exp (-β x)`.
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

/-- Equality between a finite nonnegative weighted sum of exponential values and the corresponding
weighted tangent values forces every point with positive weight to be the tangency point. -/
theorem exp_tangent_weighted_sum_eq_support
    {ι : Type*} [Fintype ι] (β x₀ : ℝ) (hβ : β ≠ 0)
    (w E : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (heq :
      ∑ i, w i *
          ((-β * Real.exp (-β * x₀)) * E i +
            (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) =
        ∑ i, w i * Real.exp (-β * E i)) :
    ∀ i, 0 < w i → E i = x₀ := by
  have hgap_nonneg (i : ι) :
      0 ≤ Real.exp (-β * E i) -
        ((-β * Real.exp (-β * x₀)) * E i +
          (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) :=
    sub_nonneg.mpr (exp_tangent β x₀ (E i))
  have hsumzero :
      ∑ i, w i *
          (Real.exp (-β * E i) -
            ((-β * Real.exp (-β * x₀)) * E i +
              (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀))) = 0 := by
    calc
      _ = (∑ i, w i * Real.exp (-β * E i)) -
          ∑ i, w i *
            ((-β * Real.exp (-β * x₀)) * E i +
              (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := sub_eq_zero.mpr heq.symm
  have htermzero : ∀ i, w i *
      (Real.exp (-β * E i) -
        ((-β * Real.exp (-β * x₀)) * E i +
          (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀))) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j) (hgap_nonneg j))).mp hsumzero i (Finset.mem_univ i)
  intro i hwi
  have hgapzero :
      Real.exp (-β * E i) -
        ((-β * Real.exp (-β * x₀)) * E i +
          (Real.exp (-β * x₀) - (-β * Real.exp (-β * x₀)) * x₀)) = 0 :=
    (mul_eq_zero.mp (htermzero i)).resolve_left hwi.ne'
  apply (exp_tangent_eq_iff β x₀ (E i) hβ).mp
  linarith
