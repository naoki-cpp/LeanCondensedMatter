import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventApproximation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Strong convergence of bounded resolvent approximations

For the resolvent regularizer `Jᵣ` constructed in `ResolventApproximation`, the elementary
nonreal-resolvent estimate gives the uniform contraction bound `‖Jᵣ x‖ ≤ ‖x‖`.  On the original
operator domain one moreover has the quantitative estimate

`‖Jᵣ x - x‖ ≤ r⁻¹ ‖A x‖`.

Density of the domain then upgrades this to strong convergence `Jᵣ x → x` for every vector as
`r → +∞`.  Combined with `Aᵣ x = Jᵣ (A x)`, this also gives `Aᵣ x → A x` on the generator domain.
These convergence estimates connect the bounded self-adjoint approximants to the original generator
in the Stone-theorem construction.
-/

namespace LinearPMap

noncomputable section

open Complex Filter Set
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    (((r : ℂ) * I).im) ≠ 0 := by
  simpa using ne_of_gt hr

private theorem star_imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    ((star ((r : ℂ) * I)).im) ≠ 0 := by
  simpa using neg_ne_zero.mpr (ne_of_gt hr)

private theorem norm_resolvent_imaginaryParameter_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (y : H) :
    ‖nonrealResolvent A hA ((r : ℂ) * I) (imaginaryParameter_im_ne_zero hr) y‖ ≤
      r⁻¹ * ‖y‖ := by
  simpa [abs_of_pos hr] using
    norm_nonrealResolvent_le A hA ((r : ℂ) * I) (imaginaryParameter_im_ne_zero hr) y

private theorem norm_resolvent_star_imaginaryParameter_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (y : H) :
    ‖nonrealResolvent A hA (star ((r : ℂ) * I))
        (star_imaginaryParameter_im_ne_zero hr) y‖ ≤ r⁻¹ * ‖y‖ := by
  simpa [abs_of_pos hr] using
    norm_nonrealResolvent_le A hA (star ((r : ℂ) * I))
      (star_imaginaryParameter_im_ne_zero hr) y

/-- The resolvent regularizers are contractions, uniformly in the positive scale `r`. -/
theorem norm_resolventRegularizer_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (y : H) :
    ‖resolventRegularizer A hA r hr y‖ ≤ ‖y‖ := by
  have hminus := norm_resolvent_star_imaginaryParameter_le A hA r hr y
  have hplus := norm_resolvent_imaginaryParameter_le A hA r hr y
  change
    ‖(((r / 2 : ℝ) : ℂ) * I) •
        (nonrealResolvent A hA (star ((r : ℂ) * I))
            (star_imaginaryParameter_im_ne_zero hr) y -
          nonrealResolvent A hA ((r : ℂ) * I)
            (imaginaryParameter_im_ne_zero hr) y)‖ ≤ ‖y‖
  rw [norm_smul]
  have hcoef : ‖(((r / 2 : ℝ) : ℂ) * I)‖ = r / 2 := by
    simp [abs_of_pos hr]
  rw [hcoef]
  calc
    (r / 2) *
        ‖nonrealResolvent A hA (star ((r : ℂ) * I))
            (star_imaginaryParameter_im_ne_zero hr) y -
          nonrealResolvent A hA ((r : ℂ) * I)
            (imaginaryParameter_im_ne_zero hr) y‖
        ≤ (r / 2) *
            (‖nonrealResolvent A hA (star ((r : ℂ) * I))
                (star_imaginaryParameter_im_ne_zero hr) y‖ +
              ‖nonrealResolvent A hA ((r : ℂ) * I)
                (imaginaryParameter_im_ne_zero hr) y‖) := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (r / 2) * (r⁻¹ * ‖y‖ + r⁻¹ * ‖y‖) := by
      gcongr
    _ = ‖y‖ := by
      field_simp [ne_of_gt hr]
      ring

/-- On the original domain the regularizer differs from the identity by the average of the two
nonreal resolvents applied to the generator. -/
theorem resolventRegularizer_apply_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r)
    (x : A.domain) :
    resolventRegularizer A hA r hr (x : H) =
      (x : H) - ((1 / 2 : ℝ) : ℂ) •
        (nonrealResolvent A hA (star ((r : ℂ) * I))
            (star_imaginaryParameter_im_ne_zero hr) (A x) +
          nonrealResolvent A hA ((r : ℂ) * I)
            (imaginaryParameter_im_ne_zero hr) (A x)) := by
  change
    (((r / 2 : ℝ) : ℂ) * I) •
        (nonrealResolvent A hA (star ((r : ℂ) * I))
            (star_imaginaryParameter_im_ne_zero hr) (x : H) -
          nonrealResolvent A hA ((r : ℂ) * I)
            (imaginaryParameter_im_ne_zero hr) (x : H)) = _
  rw [nonrealResolvent_apply_operator A hA (star ((r : ℂ) * I))
      (star_imaginaryParameter_im_ne_zero hr) x,
    nonrealResolvent_apply_operator A hA ((r : ℂ) * I)
      (imaginaryParameter_im_ne_zero hr) x]
  simp
  module

/-- Quantitative domain estimate for the regularizer error. -/
theorem norm_resolventRegularizer_sub_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r)
    (x : A.domain) :
    ‖resolventRegularizer A hA r hr (x : H) - (x : H)‖ ≤ r⁻¹ * ‖A x‖ := by
  rw [resolventRegularizer_apply_domain A hA r hr x]
  have hminus := norm_resolvent_star_imaginaryParameter_le A hA r hr (A x)
  have hplus := norm_resolvent_imaginaryParameter_le A hA r hr (A x)
  have hdiff :
      (x : H) - ((1 / 2 : ℝ) : ℂ) •
          (nonrealResolvent A hA (star ((r : ℂ) * I))
              (star_imaginaryParameter_im_ne_zero hr) (A x) +
            nonrealResolvent A hA ((r : ℂ) * I)
              (imaginaryParameter_im_ne_zero hr) (A x)) - (x : H) =
        -(((1 / 2 : ℝ) : ℂ) •
          (nonrealResolvent A hA (star ((r : ℂ) * I))
              (star_imaginaryParameter_im_ne_zero hr) (A x) +
            nonrealResolvent A hA ((r : ℂ) * I)
              (imaginaryParameter_im_ne_zero hr) (A x))) := by
    module
  rw [hdiff, norm_neg, norm_smul]
  have hhalf : ‖(((1 / 2 : ℝ) : ℂ))‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  calc
    (1 / 2 : ℝ) *
        ‖nonrealResolvent A hA (star ((r : ℂ) * I))
            (star_imaginaryParameter_im_ne_zero hr) (A x) +
          nonrealResolvent A hA ((r : ℂ) * I)
            (imaginaryParameter_im_ne_zero hr) (A x)‖
        ≤ (1 / 2 : ℝ) *
            (‖nonrealResolvent A hA (star ((r : ℂ) * I))
                (star_imaginaryParameter_im_ne_zero hr) (A x)‖ +
              ‖nonrealResolvent A hA ((r : ℂ) * I)
                (imaginaryParameter_im_ne_zero hr) (A x)‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (r⁻¹ * ‖A x‖ + r⁻¹ * ‖A x‖) := by
      gcongr
    _ = r⁻¹ * ‖A x‖ := by ring

/-- Strong convergence of the resolvent regularizer, written directly in epsilon form. -/
theorem resolventRegularizer_strong_convergence
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (y : H) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∀ hr : 0 < r,
      ‖resolventRegularizer A hA r hr y - y‖ < ε := by
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨x0, hxball, hxdom⟩ :=
    (Metric.dense_iff.mp hA.dense_domain y (ε / 4) hquarter)
  let x : A.domain := ⟨x0, hxdom⟩
  have hxy : ‖(x : H) - y‖ < ε / 4 := by
    simpa [x, dist_eq_norm, norm_sub_rev] using hxball
  let R : ℝ := 1 + 2 * ‖A x‖ / ε
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hRpos, ?_⟩
  intro r hRr hr
  have hratio : 2 * ‖A x‖ / ε < r := by
    dsimp [R] at hRr
    linarith
  have hmiddle : r⁻¹ * ‖A x‖ < ε / 2 := by
    have hmul : 2 * ‖A x‖ < r * ε := by
      exact (div_lt_iff₀ hε).mp (by simpa [mul_comm] using hratio)
    rw [inv_mul_eq_div]
    apply (div_lt_iff₀ hr).2
    nlinarith
  let J := resolventRegularizer A hA r hr
  have hdecomp :
      J y - y = J (y - (x : H)) + (J (x : H) - (x : H)) + ((x : H) - y) := by
    have hmap : J (y - (x : H)) = J y - J (x : H) := J.map_sub _ _
    rw [hmap]
    module
  rw [hdecomp]
  have hfirst : ‖J (y - (x : H))‖ < ε / 4 := by
    calc
      ‖J (y - (x : H))‖ ≤ ‖y - (x : H)‖ :=
        norm_resolventRegularizer_le A hA r hr (y - (x : H))
      _ = ‖(x : H) - y‖ := norm_sub_rev _ _
      _ < ε / 4 := hxy
  have hsecond : ‖J (x : H) - (x : H)‖ < ε / 2 := by
    exact lt_of_le_of_lt (norm_resolventRegularizer_sub_le A hA r hr x) hmiddle
  calc
    ‖J (y - (x : H)) + (J (x : H) - (x : H)) + ((x : H) - y)‖
        ≤ ‖J (y - (x : H)) + (J (x : H) - (x : H))‖ + ‖(x : H) - y‖ :=
          norm_add_le _ _
    _ ≤ (‖J (y - (x : H))‖ + ‖J (x : H) - (x : H)‖) + ‖(x : H) - y‖ := by
      gcongr
      exact norm_add_le _ _
    _ < (ε / 4 + ε / 2) + ε / 4 := by gcongr
    _ = ε := by ring

/-- The bounded generator approximants converge to the original generator on its domain. -/
theorem boundedSelfAdjointApproximation_strong_convergence
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (x : A.domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∀ hr : 0 < r,
      ‖boundedSelfAdjointApproximation A hA r hr (x : H) - A x‖ < ε := by
  obtain ⟨R, hR, hconv⟩ :=
    resolventRegularizer_strong_convergence A hA (A x) ε hε
  refine ⟨R, hR, ?_⟩
  intro r hRr hr
  rw [boundedSelfAdjointApproximation_apply_domain A hA r hr x]
  exact hconv r hRr hr

end

end LinearPMap
