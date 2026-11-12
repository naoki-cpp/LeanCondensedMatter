import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Quadratic-resolvent radial integration

A model-independent finite-interval primitive for a squared quadratic resolvent with
a nonzero real scale. The complex spectral center is arbitrary provided the denominator
does not vanish along the real integration variable. No logarithm branch or physical
broadening assumptions are needed.
-/

namespace MeasureTheory

noncomputable section

open scoped Interval

/-- The weighted squared inverse of a nonvanishing quadratic complex resolvent has an
elementary rational primitive. The scale may have either sign; integration is over the
oriented real interval from zero to the specified endpoint. -/
theorem intervalIntegrable_and_integral_quadraticResolventInverseSquare
    (scale pMax : ℝ) (A : ℂ) (hscale : scale ≠ 0)
    (hden : ∀ p : ℝ, A - ((scale ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0) :
    IntervalIntegrable
        (fun p : ℝ => (p : ℂ) * A * (A - (((scale ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)
        volume 0 pMax ∧
      (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) * A * (A - (((scale ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2) =
        ((((2 * scale ^ 2 : ℝ) : ℂ))⁻¹ * A) *
          ((A - (((scale ^ 2 * pMax ^ 2 : ℝ) : ℂ)))⁻¹ - A⁻¹) := by
  let c : ℂ := ((scale ^ 2 : ℝ) : ℂ)
  let g : ℂ → ℂ := fun z => A - c * z ^ 2
  let F : ℂ → ℂ := fun z => ((2 : ℂ) * c)⁻¹ * A * (g z)⁻¹
  have hscaleC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale
  have hg : ∀ p : ℝ, HasDerivAt g (-2 * c * (p : ℂ)) (p : ℂ) := by
    intro p
    dsimp [g]
    convert! ((hasDerivAt_pow 2 (p : ℂ)).const_mul c).const_sub A using 1
    all_goals ring
  have hF : ∀ p : ℝ,
      HasDerivAt (fun x : ℝ => F (x : ℂ))
        ((p : ℂ) * A * (A - (((scale ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2) p := by
    intro p
    have hgp : g (p : ℂ) ≠ 0 := by simpa [g, c] using hden p
    have hreal := (((hg p).inv hgp).const_mul (((2 : ℂ) * c)⁻¹ * A)).comp_ofReal
    convert hreal using 1
    dsimp [g, c] at hgp ⊢
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp [hgp, hscaleC]
  have hinv : Continuous (fun p : ℝ =>
      (A - (((scale ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹) :=
    (show Continuous (fun p : ℝ => A - (((scale ^ 2 * p ^ 2 : ℝ) : ℂ))) by fun_prop).inv₀ hden
  have hint : IntervalIntegrable
      (fun p : ℝ => (p : ℂ) * A * (A - (((scale ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)
      volume 0 pMax := by
    apply Continuous.intervalIntegrable
    exact ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const).mul (hinv.pow 2)
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun p _ => hF p) hint]
  simp [F, g, c, sub_eq_add_neg, mul_assoc]
  ring

end

end MeasureTheory
