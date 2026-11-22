import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Decay from a two-component radial first-order differential system

An elementary Lyapunov energy estimate for real solutions of
`x' = -y`, `y' = x - y/r` on `r ≥ 2`.
The decay follows from the corrected energy without invoking
Bessel asymptotics, Fourier analysis, or any physical model.
-/

namespace RadialODE

/-- A quantitative Lyapunov argument for the two-component radial first-order system.
The corrected energy `F = x² + y² - xy/r` obeys
`d/dr (r F²) = F (-x²-y²+3xy/r) ≤ 0` for `r ≥ 2`.
Consequently the energy tends to zero without invoking an asymptotic
special-function asymptotics. -/
theorem energy_tendsto_zero_of_firstOrderSystem
    (x y : ℝ → ℝ)
    (hx : ∀ r : ℝ, 2 ≤ r → HasDerivAt x (-y r) r)
    (hy : ∀ r : ℝ, 2 ≤ r → HasDerivAt y (x r - y r / r) r) :
    Filter.Tendsto (fun r : ℝ => x r ^ 2 + y r ^ 2)
      Filter.atTop (nhds 0) := by
  let E : ℝ → ℝ := fun r => x r ^ 2 + y r ^ 2
  let F : ℝ → ℝ := fun r => E r - x r * y r / r
  let H : ℝ → ℝ := fun r => r * F r ^ 2
  have hE_nonneg (r : ℝ) : 0 ≤ E r := by
    dsimp [E]
    positivity
  have hE_le_two_F (r : ℝ) (hr : 2 ≤ r) : E r ≤ 2 * F r := by
    have hxy : 2 * (x r * y r) ≤ E r := by
      dsimp [E]
      nlinarith [sq_nonneg (x r - y r)]
    have hrE : 0 ≤ (r - 1) * E r :=
      mul_nonneg (by linarith) (hE_nonneg r)
    have hxy' : 2 * (x r * y r) ≤ r * E r := by
      nlinarith [hxy, hrE]
    have hdiv : 2 * (x r * y r) / r ≤ E r :=
      (div_le_iff₀ (by linarith : 0 < r)).2 (by nlinarith [hxy'])
    have hrewrite : 2 * (x r * y r / r) = 2 * (x r * y r) / r := by ring
    rw [← hrewrite] at hdiv
    dsimp [F]
    linarith
  have hF_nonneg (r : ℝ) (hr : 2 ≤ r) : 0 ≤ F r := by
    linarith [hE_nonneg r, hE_le_two_F r hr]
  have hH_hasDerivAt (r : ℝ) (hr : 2 ≤ r) :
      HasDerivAt H
        (F r * (-E r + 3 * (x r * y r) / r)) r := by
    have hrne : r ≠ 0 := ne_of_gt (by linarith : 0 < r)
    have hxr := hx r hr
    have hyr := hy r hr
    have hE' := (hxr.pow 2).add (hyr.pow 2)
    have hquot := (hxr.mul hyr).div (hasDerivAt_id r) hrne
    have hF' := hE'.sub hquot
    have hH' := (hasDerivAt_id r).mul (hF'.pow 2)
    convert hH' using 1
    · rfl
    · dsimp [E, F, H]
      field_simp [hrne]
      ring
  have hH_deriv_nonpos (r : ℝ) (hr : 2 ≤ r) :
      F r * (-E r + 3 * (x r * y r) / r) ≤ 0 := by
    have hxy : 2 * (x r * y r) ≤ E r := by
      dsimp [E]
      nlinarith [sq_nonneg (x r - y r)]
    have hrE : 0 ≤ (r - 2) * E r :=
      mul_nonneg (by linarith) (hE_nonneg r)
    have hxy' : 3 * (x r * y r) ≤ r * E r := by
      nlinarith [hxy, hrE, hE_nonneg r]
    have hdiv : 3 * (x r * y r) / r ≤ E r :=
      (div_le_iff₀ (by linarith : 0 < r)).2 (by nlinarith [hxy'])
    exact mul_nonpos_of_nonneg_of_nonpos (hF_nonneg r hr) (by linarith)
  have hanti : AntitoneOn H (Set.Ici (2 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (2 : ℝ))
    · intro r hr
      exact (hH_hasDerivAt r hr).continuousAt.continuousWithinAt
    · intro r hr
      have hr' : 2 ≤ r := by
        have hgt : 2 < r := by
          simpa only [interior_Ici, Set.mem_Ioi] using hr
        linarith
      exact (hH_hasDerivAt r hr').differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : 2 ≤ r := by
        have hgt : 2 < r := by
          simpa only [interior_Ici, Set.mem_Ioi] using hr
        linarith
      rw [(hH_hasDerivAt r hr').deriv]
      exact hH_deriv_nonpos r hr'
  have hSqBound (r : ℝ) (hr : 2 ≤ r) :
      F r ^ 2 ≤ H 2 / r := by
    have hupper := hanti (show (2 : ℝ) ∈ Set.Ici 2 by norm_num)
      (Set.mem_Ici.mpr hr) hr
    apply (le_div_iff₀ (by linarith : 0 < r)).2
    simpa only [H, mul_comm] using hupper
  have hUpperLim :
      Filter.Tendsto (fun r : ℝ => H 2 / r) Filter.atTop (nhds 0) := by
    simpa only [id_eq] using
      (Filter.tendsto_id : Filter.Tendsto (fun r : ℝ => r)
        Filter.atTop Filter.atTop).const_div_atTop (H 2)
  have hSqLim : Filter.Tendsto (fun r : ℝ => F r ^ 2)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact sq_nonneg (F r)
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact hSqBound r hr
    · exact hUpperLim
  have hFLim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have hroot : Filter.Tendsto (fun r : ℝ => Real.sqrt (F r ^ 2))
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp hSqLim
    apply hroot.congr'
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hF_nonneg r hr)]
  have hDouble : Filter.Tendsto (fun r : ℝ => 2 * F r)
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hFLim) using 1
    norm_num
  have hELim : Filter.Tendsto E Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact hE_nonneg r
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact hE_le_two_F r hr
    · exact hDouble
  exact hELim

end RadialODE
