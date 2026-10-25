import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Entrywise interval integration of complex matrices

These laws are independent of matrix dimensions or any physical model.
Additivity and subtraction require entrywise interval integrability; without
it, the interval integral's non-integrable convention need not preserve sums.
-/

namespace Matrix

noncomputable section

/-- Integrate a complex matrix-valued function over an interval, entry by entry. -/
def intervalIntegralEntries {ι κ : Type*}
    (a b : ℝ) (f : ℝ → Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  fun i j => ∫ p in a..b, f p i j

/-- Entrywise interval integration commutes with complex scalar multiplication. -/
theorem intervalIntegralEntries_smul {ι κ : Type*}
    (a b : ℝ) (c : ℂ) (f : ℝ → Matrix ι κ ℂ) :
    intervalIntegralEntries a b (fun p => c • f p) =
      c • intervalIntegralEntries a b f := by
  ext i j
  change (∫ p in a..b, c * f p i j) = c * (∫ p in a..b, f p i j)
  rw [intervalIntegral.integral_const_mul]

/-- Additivity holds when every matrix entry is interval-integrable. -/
theorem intervalIntegralEntries_add {ι κ : Type*}
    (a b : ℝ) (f g : ℝ → Matrix ι κ ℂ)
    (hf : ∀ i j, IntervalIntegrable (fun p => f p i j) MeasureTheory.volume a b)
    (hg : ∀ i j, IntervalIntegrable (fun p => g p i j) MeasureTheory.volume a b) :
    intervalIntegralEntries a b (fun p => f p + g p) =
      intervalIntegralEntries a b f + intervalIntegralEntries a b g := by
  ext i j
  change (∫ p in a..b, f p i j + g p i j) =
    (∫ p in a..b, f p i j) + (∫ p in a..b, g p i j)
  exact intervalIntegral.integral_add (hf i j) (hg i j)

/-- Subtraction likewise commutes with entrywise interval integration. -/
theorem intervalIntegralEntries_sub {ι κ : Type*}
    (a b : ℝ) (f g : ℝ → Matrix ι κ ℂ)
    (hf : ∀ i j, IntervalIntegrable (fun p => f p i j) MeasureTheory.volume a b)
    (hg : ∀ i j, IntervalIntegrable (fun p => g p i j) MeasureTheory.volume a b) :
    intervalIntegralEntries a b (fun p => f p - g p) =
      intervalIntegralEntries a b f - intervalIntegralEntries a b g := by
  ext i j
  change (∫ p in a..b, f p i j - g p i j) =
    (∫ p in a..b, f p i j) - (∫ p in a..b, g p i j)
  exact intervalIntegral.integral_sub (hf i j) (hg i j)

end

end Matrix
