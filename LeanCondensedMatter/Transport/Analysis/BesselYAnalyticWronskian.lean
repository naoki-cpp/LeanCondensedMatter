import LeanCondensedMatter.Analysis.PowerSeries.CoefficientSum
import LeanCondensedMatter.Transport.Analysis.BesselJFormalAnalyticBridge
import LeanCondensedMatter.Transport.Analysis.BesselYFormalAnalyticBridge
import LeanCondensedMatter.Transport.Analysis.BesselCrossedXMoment

set_option linter.style.header false

/-!
# Unconditional analytic Bessel J/Y Wronskian

Transport the normalized factorial/harmonic identity proved in
`BesselYFormalOrderOne` from ℂ⟦X⟧ to actual complex infinite sums,
using only absolutely convergent coefficientwise evaluations.
Then apply the already proved DLMF Y₀/Y₁ algebraic reduction and
instantiate the concrete real-argument Wronskian required by the
reference crossed-X Bessel integral.

This proves no identification between the physical finite-regulator
Gaussian crossed-X diagram and the reference Bessel integral.
-/

namespace QuantumTheory.Transport

noncomputable section

open scoped PowerSeries

/-- The missing harmonic identity for the *actual* Mathlib J₀/J₁ and
the absolutely convergent DLMF Y₀/Y₁ harmonic corrections. -/
theorem besselY0Y1_harmonicIdentity (z : ℂ) :
    Complex.besselJ 0 z -
        z * Complex.besselJ 1 z * besselY0HarmonicCorrection z +
        (z ^ 2 / 4) * Complex.besselJ 0 z *
          besselY1HarmonicCorrection z = 1 := by
  let x : ℂ := -(z / 2) ^ 2
  have hA : Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalJ0 * x ^ n) :=
    summable_besselFormalJ0_eval z
  have hD : Summable (fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) * x ^ n) :=
    summable_besselFormalJ0_derivative_eval z
  have hB : Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalH0 * x ^ n) :=
    summable_besselFormalH0_eval z
  have hC : Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalH1 * x ^ n) :=
    summable_besselFormalH1_eval z
  have h2D : Summable (fun n : ℕ =>
      PowerSeries.coeff n (2 * PowerSeries.derivative besselFormalJ0) * x ^ n) := by
    simpa using PowerSeries.summable_coefficientSum_C_mul
      (PowerSeries.derivative besselFormalJ0) x 2 hD
  have h2DEval :
      PowerSeries.coefficientSum (2 * PowerSeries.derivative besselFormalJ0) x =
        2 * PowerSeries.coefficientSum (PowerSeries.derivative besselFormalJ0) x := by
    simpa using PowerSeries.coefficientSum_C_mul (PowerSeries.derivative besselFormalJ0) x 2
  have h2DB :=
    PowerSeries.summable_coefficientSum_mul
      (2 * PowerSeries.derivative besselFormalJ0) besselFormalH0 x h2D hB
  have hAC :=
    PowerSeries.summable_coefficientSum_mul
      besselFormalJ0 besselFormalH1 x hA hC
  have hX2DB :=
    PowerSeries.summable_coefficientSum_X_mul
      (2 * PowerSeries.derivative besselFormalJ0 * besselFormalH0) x h2DB
  have hXAC :=
    PowerSeries.summable_coefficientSum_X_mul
      (besselFormalJ0 * besselFormalH1) x hAC
  have hAplus :=
    PowerSeries.summable_coefficientSum_add besselFormalJ0
      (PowerSeries.X * (2 * PowerSeries.derivative besselFormalJ0 *
        besselFormalH0)) x hA hX2DB
  have hFormal := congrArg
    (fun f : ℂ⟦X⟧ => PowerSeries.coefficientSum f x)
    besselFormalJ0H0H1_harmonicIdentity
  rw [PowerSeries.coefficientSum_sub _ _ x hAplus hXAC,
      PowerSeries.coefficientSum_add _ _ x hA hX2DB,
      PowerSeries.coefficientSum_X_mul
        (2 * PowerSeries.derivative besselFormalJ0 * besselFormalH0) x,
      PowerSeries.coefficientSum_X_mul (besselFormalJ0 * besselFormalH1) x,
      PowerSeries.coefficientSum_mul _ _ x h2D hB,
      PowerSeries.coefficientSum_mul _ _ x hA hC,
      h2DEval,
      PowerSeries.coefficientSum_one] at hFormal
  have hJ0 :
      PowerSeries.coefficientSum besselFormalJ0 x =
        Complex.besselJ 0 z :=
    (besselJZero_eq_formalTsum z).symm
  have hJ1 :
      (z / 2) *
          PowerSeries.coefficientSum
            (PowerSeries.derivative besselFormalJ0) x =
        Complex.besselJ 1 z :=
    (besselJOne_eq_formalDerivativeTsum z).symm
  have hY0 :
      PowerSeries.coefficientSum besselFormalH0 x =
        besselY0HarmonicCorrection z :=
    (besselY0HarmonicCorrection_eq_formalTsum z).symm
  have hY1 :
      PowerSeries.coefficientSum besselFormalH1 x =
        besselY1HarmonicCorrection z :=
    (besselY1HarmonicCorrection_eq_formalTsum z).symm
  calc
    Complex.besselJ 0 z -
        z * Complex.besselJ 1 z * besselY0HarmonicCorrection z +
        (z ^ 2 / 4) * Complex.besselJ 0 z * besselY1HarmonicCorrection z =
      PowerSeries.coefficientSum besselFormalJ0 x +
        x * (2 * PowerSeries.coefficientSum
          (PowerSeries.derivative besselFormalJ0) x *
          PowerSeries.coefficientSum besselFormalH0 x) -
        x * (PowerSeries.coefficientSum besselFormalJ0 x *
          PowerSeries.coefficientSum besselFormalH1 x) := by
        rw [← hJ0, ← hJ1, ← hY0, ← hY1]
        dsimp [x]
        ring
    _ = 1 := hFormal

/-- The actual convergent DLMF Y₀/Y₁ series satisfy the standard
normalized J/Y Wronskian for every nonzero complex argument. -/
theorem besselY0Y1Series_wronskian (z : ℂ) (hz : z ≠ 0) :
    Complex.besselJ 1 z * besselY0Series z -
      Complex.besselJ 0 z * besselY1Series z =
        (((2 / Real.pi : ℝ) : ℂ)) * z⁻¹ :=
  besselY0Y1Wronskian_of_harmonicIdentity z hz
    (besselY0Y1_harmonicIdentity z)

/-- No abstract Y₀/Y₁ Wronskian premise is required for the
specific convergent Bessel-Y implementations used in the
Gaussian crossed-X reference moment. -/
theorem crossedXBesselWronskian_concreteSeries :
    CrossedXBesselWronskian
      (fun r : ℝ => besselY0Series (r : ℂ))
      (fun r : ℝ => besselY1Series (r : ℂ)) := by
  intro r hr
  exact besselY0Y1Series_wronskian (r : ℂ) (by exact_mod_cast hr)

end

end QuantumTheory.Transport
