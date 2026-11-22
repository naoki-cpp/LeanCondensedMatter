import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

/-!
# Formal Frobenius Wronskian conservation

For two complex formal power series A and B satisfying

  X A'' + A' = A,
  X B'' + B' = B + A',

the polynomial first integral

  A² + 2X(A'B - AB')

is constant. When A(0) = 1, the constant is 1, independently of B(0).
The proof is purely algebraic in the ring of formal power series:
no convergence, integration, or analytic Bessel-function theory is required.

Special-function applications, including Bessel J/Y coefficient sequences,
belong in their respective consumer modules.
-/

namespace FrobeniusWronskian

noncomputable section

open scoped PowerSeries

/-- The algebraic first integral for the paired homogeneous/inhomogeneous
Frobenius equations. -/
noncomputable def invariant
    (A B : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  A * A +
    PowerSeries.X *
      (PowerSeries.derivative A * B - A * PowerSeries.derivative B) +
    PowerSeries.X *
      (PowerSeries.derivative A * B - A * PowerSeries.derivative B)

/-- Universal conservation of the formal Frobenius first integral. -/
theorem invariant_eq_one
    (A B : ℂ⟦X⟧)
    (hA : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative A) +
        PowerSeries.derivative A = A)
    (hB : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative B) +
        PowerSeries.derivative B = B + PowerSeries.derivative A)
    (hA0 : PowerSeries.constantCoeff A = 1) :
    invariant A B = 1 := by
  have hderiv :
      PowerSeries.derivative (invariant A B) = 0 := by
    unfold invariant
    simp only [map_add, map_sub, Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul]
    linear_combination
      (2 * B) * hA - (2 * A) * hB
  have hconst :
      PowerSeries.constantCoeff
        (invariant A B) =
          PowerSeries.constantCoeff (1 : ℂ⟦X⟧) := by
    unfold invariant
    simp [hA0, PowerSeries.constantCoeff_X]
  exact PowerSeries.derivative.ext
    (by simpa only [PowerSeries.derivative_one] using hderiv) hconst

end

end FrobeniusWronskian
