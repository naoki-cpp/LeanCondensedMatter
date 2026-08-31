import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Full-angle harmonic integrals

Model-independent trigonometric integrals used by angular reductions in transport calculations.
Only the first and second harmonics currently needed by downstream consumers are exposed here; no
general Fourier API is introduced.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- Full-angle integral of the complexified first cosine harmonic. -/
theorem integral_complex_cos_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.cos θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.cos)

/-- Full-angle integral of the complexified first sine harmonic. -/
theorem integral_complex_sin_zero_two_pi :
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
theorem integral_complex_cos_sq_sub_sin_sq_zero_two_pi :
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
theorem integral_complex_cos_mul_sin_zero_two_pi :
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

end

end Transport
end QuantumTheory
