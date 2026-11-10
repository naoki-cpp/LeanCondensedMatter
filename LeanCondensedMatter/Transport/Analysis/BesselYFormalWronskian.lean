import LeanCondensedMatter.Transport.Analysis.BesselY1Series
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

/-!
# Formal Bessel Wronskian: conservation from inhomogeneous Frobenius equations

The logarithmic/harmonic Bessel-Y corrections suggest two power series in
the variable x = -z²/4:

A(x) = Σ xⁿ/(n!)²
B(x) = Σ Hₙ xⁿ/(n!)².

They satisfy

  x A'' + A' = A,
  x B'' + B' = B + A'.

The algebraic first integral is

  A² + 2x(A' B - A B') = 1,

provided A(0)=1, B(0)=0. This is the universal formal
Wronskian conservation law. Crucially it is proved over the
**formal power series ring** and requires no convergence or
termwise differentiation theorem.

The remaining work is to instantiate the two differential
equations from the concrete harmonic coefficients and then
transfer the identity to the analytic, convergent series
already built in BesselY0Series/BesselY1Series. This module
does not postulate a Wronskian for the analytic Bessel functions.
-/

namespace QuantumTheory.Transport

noncomputable section

open scoped PowerSeries

/-- The algebraic formal Wronskian first integral. -/
noncomputable def besselFormalWronskianInvariant
    (A B : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  A * A +
    PowerSeries.X *
      (PowerSeries.derivative A * B - A * PowerSeries.derivative B) +
    PowerSeries.X *
      (PowerSeries.derivative A * B - A * PowerSeries.derivative B)

/-- Universal conservation of the Frobenius first integral in the
formal power-series ring. This gives the coefficient-level
normalization needed for the concrete J/Y Wronskian, without
assuming that analytic identity. -/
theorem besselFormalWronskianInvariant_eq_one
    (A B : ℂ⟦X⟧)
    (hA : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative A) +
        PowerSeries.derivative A = A)
    (hB : PowerSeries.X * PowerSeries.derivative (PowerSeries.derivative B) +
        PowerSeries.derivative B = B + PowerSeries.derivative A)
    (hA0 : PowerSeries.constantCoeff A = 1)
    (hB0 : PowerSeries.constantCoeff B = 0) :
    besselFormalWronskianInvariant A B = 1 := by
  let D : ℂ⟦X⟧ → ℂ⟦X⟧ := fun f => PowerSeries.derivative f
  have hderiv :
      PowerSeries.derivative (besselFormalWronskianInvariant A B) = 0 := by
    unfold besselFormalWronskianInvariant
    simp only [map_add, map_sub, Derivation.leibniz,
      PowerSeries.derivative_X, one_mul, smul_eq_mul]
    linear_combination
      (2 * B) * hA - (2 * A) * hB
  have hconst :
      PowerSeries.constantCoeff
        (besselFormalWronskianInvariant A B) =
          PowerSeries.constantCoeff (1 : ℂ⟦X⟧) := by
    unfold besselFormalWronskianInvariant
    simp [hA0, hB0, PowerSeries.constantCoeff_X]
  exact PowerSeries.derivative.ext
    (by simpa only [PowerSeries.derivative_one] using hderiv) hconst

end

end QuantumTheory.Transport
