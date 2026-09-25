import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Full-angle harmonic integrals

Model-independent real- and complex-valued trigonometric integrals used by angular reductions in
transport calculations. Constant, first, and second harmonics share one coefficient representation;
ordinary full-angle integration and phase-weighted polar Fourier reduction consume that same data.
No general Fourier API is introduced.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- Coefficients of the constant, first, and second polar-angle harmonics used by transport
reductions. The value type is generic so the same decomposition can describe scalars, matrices, or
bounded operators. -/
structure AngularHarmonicCoefficients (E : Type*) where
  /-- Constant angular harmonic. -/
  constant : E
  /-- First cosine angular harmonic. -/
  firstCosine : E
  /-- First sine angular harmonic. -/
  firstSine : E
  /-- Second cosine harmonic `cos² θ - sin² θ`. -/
  secondCosine : E
  /-- Mixed second harmonic `cos θ sin θ`. -/
  secondMixed : E

namespace AngularHarmonicCoefficients

/-- Evaluate constant, first, and second angular-harmonic coefficients at angle `θ`. -/
def eval {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (coefficients : AngularHarmonicCoefficients E) (θ : ℝ) : E :=
  coefficients.constant +
    ((Real.cos θ : ℝ) : ℂ) • coefficients.firstCosine +
    ((Real.sin θ : ℝ) : ℂ) • coefficients.firstSine +
    ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) •
      coefficients.secondCosine +
    (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) • coefficients.secondMixed

end AngularHarmonicCoefficients

/-- Full-angle integral of the complexified first cosine harmonic. -/
private theorem integral_complex_cos_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.cos θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.cos)

/-- Full-angle integral of the complexified first sine harmonic. -/
private theorem integral_complex_sin_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.sin)

/-- Full-angle integral of `cos² θ`. -/
theorem integral_cos_sq_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2) = Real.pi := by
  have hcos :
      IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ 2) volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.pow 2).intervalIntegrable 0 (2 * Real.pi)
  have hsin :
      IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ 2) volume 0 (2 * Real.pi) :=
    (Real.continuous_sin.pow 2).intervalIntegrable 0 (2 * Real.pi)
  have hdiff :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2) -
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.sin θ ^ 2) = 0 := by
    rw [← intervalIntegral.integral_sub hcos hsin]
    simpa using
      (integral_cos_sq_sub_sin_sq (a := (0 : ℝ)) (b := 2 * Real.pi))
  have hsum :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2) +
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.sin θ ^ 2) = 2 * Real.pi := by
    rw [← intervalIntegral.integral_add hcos hsin]
    calc
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ 2 + Real.sin θ ^ 2) =
          ∫ _θ : ℝ in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            nlinarith [Real.sin_sq_add_cos_sq θ]
      _ = 2 * Real.pi := by simp
  linarith

/-- The complexified second cosine harmonic integrates to zero over a full polar angle. -/
private theorem integral_complex_cos_sq_sub_sin_sq_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℂ) ^ 2) - ((Real.sin θ : ℂ) ^ 2)) = 0 := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((Real.cos θ : ℂ) ^ 2) - ((Real.sin θ : ℂ) ^ 2)) =
        (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          (((Real.cos θ ^ 2 - Real.sin θ ^ 2 : ℝ) : ℂ))) := by
            apply intervalIntegral.integral_congr
            intro θ _
            push_cast
            rfl
    _ = (((∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          Real.cos θ ^ 2 - Real.sin θ ^ 2) : ℝ) : ℂ) := by
            exact @intervalIntegral.integral_ofReal
              (0 : ℝ) (2 * Real.pi) volume
              (fun θ : ℝ => Real.cos θ ^ 2 - Real.sin θ ^ 2)
    _ = 0 := by
      rw [integral_cos_sq_sub_sin_sq]
      simp

/-- The complexified mixed second harmonic integrates to zero over a full polar angle. -/
private theorem integral_complex_cos_mul_sin_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) =
        (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          (((Real.sin θ * Real.cos θ : ℝ) : ℂ))) := by
            apply intervalIntegral.integral_congr
            intro θ _
            push_cast
            ring
    _ = (((∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          Real.sin θ * Real.cos θ) : ℝ) : ℂ) := by
            exact @intervalIntegral.integral_ofReal
              (0 : ℝ) (2 * Real.pi) volume
              (fun θ : ℝ => Real.sin θ * Real.cos θ)
    _ = 0 := by
      have hreal :
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), Real.sin θ * Real.cos θ) = 0 := by
        simpa using
          (integral_sin_pow_mul_cos_pow_odd (a := (0 : ℝ)) (b := 2 * Real.pi) 1 0)
      rw [hreal]
      simp

/-- Ordinary full-angle integration of the canonical constant/first/second harmonic decomposition.
All nonconstant channels vanish. -/
theorem AngularHarmonicCoefficients.integral_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (coefficients : AngularHarmonicCoefficients E) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), coefficients.eval θ) =
      (2 * Real.pi : ℝ) • coefficients.constant := by
  have hconst : IntervalIntegrable (fun _θ : ℝ => coefficients.constant) volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hcos : IntervalIntegrable
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) • coefficients.firstCosine)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsin : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) • coefficients.firstSine)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsecond : IntervalIntegrable
      (fun θ : ℝ =>
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) •
          coefficients.secondCosine) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmixed : IntervalIntegrable
      (fun θ : ℝ =>
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) • coefficients.secondMixed)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold AngularHarmonicCoefficients.eval
  rw [intervalIntegral.integral_add (((hconst.add hcos).add hsin).add hsecond) hmixed,
    intervalIntegral.integral_add ((hconst.add hcos).add hsin) hsecond,
    intervalIntegral.integral_add (hconst.add hcos) hsin,
    intervalIntegral.integral_add hconst hcos,
    intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const,
    integral_complex_cos_zero_two_pi,
    integral_complex_sin_zero_two_pi,
    integral_complex_cos_sq_sub_sin_sq_zero_two_pi,
    integral_complex_cos_mul_sin_zero_two_pi]
  simp

/-- A complex linear combination of the first sine and cosine harmonics integrates to zero. -/
theorem integral_complex_cos_mul_add_sin_mul_zero_two_pi (cCos cSin : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℝ) : ℂ) * cCos + ((Real.sin θ : ℝ) : ℂ) * cSin) = 0 := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := 0
      firstCosine := cCos
      firstSine := cSin
      secondCosine := 0
      secondMixed := 0 }
  simpa [coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul] using coefficients.integral_eval

/-- Full-angle integral of a real quadratic polynomial in the first cosine harmonic. -/
theorem integral_quadratic_cos_zero_two_pi (a b c : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      a + b * Real.cos θ + c * Real.cos θ ^ 2) =
      2 * Real.pi * a + Real.pi * c := by
  have hconst : IntervalIntegrable (fun _θ : ℝ => a) volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable 0 (2 * Real.pi)
  have hcos : IntervalIntegrable (fun θ : ℝ => b * Real.cos θ) volume 0 (2 * Real.pi) :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable 0 (2 * Real.pi)
  have hcosSq : IntervalIntegrable
      (fun θ : ℝ => c * Real.cos θ ^ 2) volume 0 (2 * Real.pi) :=
    (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable 0 (2 * Real.pi)
  rw [intervalIntegral.integral_add (hconst.add hcos) hcosSq,
    intervalIntegral.integral_add hconst hcos,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos, integral_cos_sq_zero_two_pi]
  simp
  ring

end

end Transport
end QuantumTheory
