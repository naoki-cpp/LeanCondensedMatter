import LeanCondensedMatter.Analysis.Operator.Unbounded.BoundedResolvent
import LeanCondensedMatter.Analysis.Operator.Unbounded.CayleyTransform
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-!
# Bounded resolvent approximations of a self-adjoint generator

For a self-adjoint partial operator `A` and a positive real scale `r`, write

`R₊ = (A - i r)⁻¹`, `R₋ = (A + i r)⁻¹`.

The symmetric resolvent combinations

`Jᵣ = (i r / 2) (R₋ - R₊)`

and

`Aᵣ = (r² / 2) (R₊ + R₋)`

are bounded self-adjoint operators.  The first is the standard resolvent regularizer and the second
is the corresponding bounded approximation of the unbounded generator.  On the original operator
domain they satisfy `Aᵣ x = Jᵣ (A x)`.  This is the rational approximation layer used in the
Stone-theorem construction. Approximants at positive scales commute by the resolvent identity.
The regularizers are contractions with domain error `‖Jᵣ x - x‖ ≤ r⁻¹ ‖A x‖`. Density then gives
strong convergence to the identity on all vectors, and the approximants converge to the original
generator on its domain.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private noncomputable def imaginaryParameter (r : ℝ) : ℂ :=
  (r : ℂ) * I

private theorem imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    (((r : ℂ) * I).im) ≠ 0 := by
  simpa using ne_of_gt hr

private theorem star_imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    ((star ((r : ℂ) * I)).im) ≠ 0 := by
  simpa using neg_ne_zero.mpr (ne_of_gt hr)

private noncomputable def regularizerCoefficient (r : ℝ) : ℂ :=
  ((r / 2 : ℝ) : ℂ) * I

private noncomputable def approximationCoefficient (r : ℝ) : ℂ :=
  ((r ^ 2 / 2 : ℝ) : ℂ)

/-- The bounded symmetric resolvent regularizer
`Jᵣ = (i r / 2) ((A + i r)⁻¹ - (A - i r)⁻¹)`. -/
noncomputable def resolventRegularizer
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  regularizerCoefficient r •
    (nonrealResolvent A hA (star (imaginaryParameter r))
        (star_imaginaryParameter_im_ne_zero hr) -
      nonrealResolvent A hA (imaginaryParameter r) (imaginaryParameter_im_ne_zero hr))

@[simp]
theorem resolventRegularizer_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (y : H) :
    resolventRegularizer A hA r hr y =
      regularizerCoefficient r •
        (nonrealResolvent A hA (star (imaginaryParameter r))
            (star_imaginaryParameter_im_ne_zero hr) y -
          nonrealResolvent A hA (imaginaryParameter r) (imaginaryParameter_im_ne_zero hr) y) := by
  rfl

/-- The resolvent regularizer is self-adjoint. -/
theorem resolventRegularizer_isSelfAdjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) :
    IsSelfAdjoint (resolventRegularizer A hA r hr) := by
  have hstar : star (regularizerCoefficient r) = -regularizerCoefficient r := by
    simp [regularizerCoefficient]
  rw [isSelfAdjoint_iff]
  simp only [resolventRegularizer, star_smul, star_sub,
    ContinuousLinearMap.star_eq_adjoint, nonrealResolvent_adjoint,
    hstar, star_star]
  module

/-- The bounded self-adjoint resolvent approximation
`Aᵣ = (r² / 2) ((A - i r)⁻¹ + (A + i r)⁻¹)`. -/
noncomputable def boundedSelfAdjointApproximation
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) : H →L[ℂ] H :=
  approximationCoefficient r •
    (nonrealResolvent A hA (imaginaryParameter r) (imaginaryParameter_im_ne_zero hr) +
      nonrealResolvent A hA (star (imaginaryParameter r))
        (star_imaginaryParameter_im_ne_zero hr))

@[simp]
theorem boundedSelfAdjointApproximation_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) (y : H) :
    boundedSelfAdjointApproximation A hA r hr y =
      approximationCoefficient r •
        (nonrealResolvent A hA (imaginaryParameter r) (imaginaryParameter_im_ne_zero hr) y +
          nonrealResolvent A hA (star (imaginaryParameter r))
            (star_imaginaryParameter_im_ne_zero hr) y) := by
  rfl

/-- Each bounded generator approximation is self-adjoint. -/
theorem boundedSelfAdjointApproximation_isSelfAdjoint
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r) :
    IsSelfAdjoint (boundedSelfAdjointApproximation A hA r hr) := by
  have hstar : star (approximationCoefficient r) = approximationCoefficient r := by
    simp [approximationCoefficient]
  rw [isSelfAdjoint_iff]
  simp only [boundedSelfAdjointApproximation, star_smul, star_add,
    ContinuousLinearMap.star_eq_adjoint, nonrealResolvent_adjoint,
    hstar, star_star]
  module

/-- On the original domain, the bounded generator approximation is the regularized generator:
`Aᵣ x = Jᵣ (A x)`. -/
theorem boundedSelfAdjointApproximation_apply_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (r : ℝ) (hr : 0 < r)
    (x : A.domain) :
    boundedSelfAdjointApproximation A hA r hr (x : H) =
      resolventRegularizer A hA r hr (A x) := by
  rw [boundedSelfAdjointApproximation_apply, resolventRegularizer_apply,
    nonrealResolvent_apply_operator A hA (star (imaginaryParameter r))
      (star_imaginaryParameter_im_ne_zero hr) x,
    nonrealResolvent_apply_operator A hA (imaginaryParameter r)
      (imaginaryParameter_im_ne_zero hr) x]
  simp only [regularizerCoefficient, approximationCoefficient, imaginaryParameter]
  match_scalars <;> simp <;> ring_nf <;> simp [pow_two] <;> ring

/-- Bounded self-adjoint resolvent approximants at two positive scales commute. -/
theorem boundedSelfAdjointApproximation_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Commute (boundedSelfAdjointApproximation A hA r hr)
      (boundedSelfAdjointApproximation A hA s hs) := by
  unfold boundedSelfAdjointApproximation
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.add_left
  · apply Commute.add_right
    · apply nonrealResolvent_commute
    · apply nonrealResolvent_commute
  · apply Commute.add_right
    · apply nonrealResolvent_commute
    · apply nonrealResolvent_commute

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
