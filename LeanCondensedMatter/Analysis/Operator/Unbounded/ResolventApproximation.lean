import LeanCondensedMatter.Analysis.Operator.Unbounded.CayleyTransform
import Mathlib.Tactic

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
Stone-theorem construction.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private noncomputable def imaginaryParameter (r : ℝ) : ℂ :=
  (r : ℂ) * I

@[simp]
private theorem imaginaryParameter_im (r : ℝ) : (imaginaryParameter r).im = r := by
  simp [imaginaryParameter]

@[simp]
private theorem star_imaginaryParameter (r : ℝ) :
    star (imaginaryParameter r) = imaginaryParameter (-r) := by
  simp [imaginaryParameter, mul_comm]

private theorem imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    (imaginaryParameter r).im ≠ 0 := by
  simpa using ne_of_gt hr

private theorem star_imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    (star (imaginaryParameter r)).im ≠ 0 := by
  simpa using neg_ne_zero.mpr (ne_of_gt hr)

private noncomputable def regularizerCoefficient (r : ℝ) : ℂ :=
  ((r / 2 : ℝ) : ℂ) * I

@[simp]
private theorem star_regularizerCoefficient (r : ℝ) :
    star (regularizerCoefficient r) = -regularizerCoefficient r := by
  simp [regularizerCoefficient]

private noncomputable def approximationCoefficient (r : ℝ) : ℂ :=
  ((r ^ 2 / 2 : ℝ) : ℂ)

@[simp]
private theorem star_approximationCoefficient (r : ℝ) :
    star (approximationCoefficient r) = approximationCoefficient r := by
  simp [approximationCoefficient]

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
  rw [isSelfAdjoint_iff]
  simp only [resolventRegularizer, star_smul, star_sub,
    ContinuousLinearMap.star_eq_adjoint, nonrealResolvent_adjoint,
    star_regularizerCoefficient, star_star]
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
  rw [isSelfAdjoint_iff]
  simp only [boundedSelfAdjointApproximation, star_smul, star_add,
    ContinuousLinearMap.star_eq_adjoint, nonrealResolvent_adjoint,
    star_approximationCoefficient, star_star]
  module

/-- Resolvents commute with applying the generator on its domain in the expected affine form. -/
theorem nonrealResolvent_apply_operator
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (x : A.domain) :
    nonrealResolvent A hA z hz (A x) =
      (x : H) + z • nonrealResolvent A hA z hz (x : H) := by
  have h := nonrealResolvent_shift_apply A hA z hz x
  calc
    nonrealResolvent A hA z hz (A x) =
        nonrealResolvent A hA z hz ((A x - z • (x : H)) + z • (x : H)) := by
      congr 1
      module
    _ = nonrealResolvent A hA z hz (A x - z • (x : H)) +
        nonrealResolvent A hA z hz (z • (x : H)) := by
      exact (nonrealResolvent A hA z hz).map_add _ _
    _ = nonrealResolvent A hA z hz (A x - z • (x : H)) +
        z • nonrealResolvent A hA z hz (x : H) := by
      congr 1
      exact (nonrealResolvent A hA z hz).map_smul z (x : H)
    _ = (x : H) + z • nonrealResolvent A hA z hz (x : H) := by
      rw [h]

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

end

end LinearPMap
