import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

/-!
# Formal Frobenius Wronskian conservation

For two formal power series A and B over a commutative rational algebra satisfying

  X A'' + A' = A,
  X B'' + B' = B + A',

the polynomial first integral

  A² + 2X(A'B - AB')

is constant and equal to A(0)², independently of B(0). In particular, it is 1 when A(0) = 1.
The proof is purely algebraic in the ring of formal power series:
no convergence, integration, or analytic Bessel-function theory is required.

Special-function applications, including Bessel J/Y coefficient sequences,
belong in their respective consumer modules.
-/

namespace FrobeniusWronskian

noncomputable section

open scoped PowerSeries

variable {R : Type*} [CommRing R]

/-- Coefficients of the formal Frobenius differential operator. -/
theorem coeff_derivative_X_mul_derivative (A : R⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative
      (PowerSeries.X * PowerSeries.derivative A)) =
        ((n + 1 : ℕ) : R) ^ 2 * PowerSeries.coeff (n + 1) A := by
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The algebraic first integral for the paired homogeneous/inhomogeneous
Frobenius equations. -/
noncomputable def invariant
    (A B : R⟦X⟧) : R⟦X⟧ :=
  A * A +
    PowerSeries.X *
      (PowerSeries.derivative A * B - A * PowerSeries.derivative B) +
    PowerSeries.X *
      (PowerSeries.derivative A * B - A * PowerSeries.derivative B)

/-- The formal first integral equals the square of the initial constant coefficient.
Only commutative rational-algebra structure is needed, not complex analysis or convergence. -/
theorem invariant_eq_C_square [Algebra ℚ R]
    (A B : R⟦X⟧)
    (hA : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative A) +
        PowerSeries.derivative A = A)
    (hB : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative B) +
        PowerSeries.derivative B = B + PowerSeries.derivative A) :
    invariant A B = PowerSeries.C ((PowerSeries.constantCoeff A) ^ 2) := by
  have hderiv :
      PowerSeries.derivative (invariant A B) = 0 := by
    unfold invariant
    simp only [map_add, map_sub, Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul]
    linear_combination
      (2 * B) * hA - (2 * A) * hB
  have hconst :
      PowerSeries.constantCoeff (invariant A B) =
        PowerSeries.constantCoeff (PowerSeries.C ((PowerSeries.constantCoeff A) ^ 2)) := by
    simp [invariant, PowerSeries.constantCoeff_X, pow_two]
  letI : HasUniqueDiv R := .of_module_rat R
  exact PowerSeries.derivative.ext
    (by simpa only [PowerSeries.derivative_C] using hderiv) hconst

/-- Unit normalization of the generic formal Frobenius invariant. -/
theorem invariant_eq_one [Algebra ℚ R]
    (A B : R⟦X⟧)
    (hA : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative A) +
        PowerSeries.derivative A = A)
    (hB : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative B) +
        PowerSeries.derivative B = B + PowerSeries.derivative A)
    (hA0 : PowerSeries.constantCoeff A = 1) :
    invariant A B = 1 := by
  rw [invariant_eq_C_square A B hA hB, hA0]
  simp

end

end FrobeniusWronskian
