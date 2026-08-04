import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticIntegrability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-!
# Finite-dimensional Lehmann-mode bridge

This module isolates the analytic denominator appearing in a finite-dimensional Lehmann
representation.  With the repository conventions

`A_I(t) = U₀(-t) A U₀(t)` and `exp (+i ω t)`,

a transition with energy gap `ΔE = Eₘ - Eₙ` contributes the damped mode

`exp ((-η + i (ω + ΔE / ℏ)) t)`.

For every `η > 0`, its causal half-line integral is

`1 / (η - i (ω + ΔE / ℏ))`.

The operator-theoretic finite-dimensional spectral decomposition is built on top of this scalar
lemma.  The switching-rate limit `η → 0⁺` is intentionally not formed here.
-/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

/-- Complex exponent of one adiabatically damped Lehmann transition mode. -/
noncomputable def lehmannModeExponent
    (hbar omega eta energyGap : ℝ) : ℂ :=
  -(eta : ℂ) + Complex.I * ((omega + energyGap / hbar : ℝ) : ℂ)

/-- The real part of a Lehmann-mode exponent is exactly the negative switching rate. -/
@[simp]
theorem lehmannModeExponent_re
    (hbar omega eta energyGap : ℝ) :
    (lehmannModeExponent hbar omega eta energyGap).re = -eta := by
  simp [lehmannModeExponent]

/-- A single causal Lehmann transition mode. -/
noncomputable def lehmannMode
    (hbar omega eta energyGap : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (lehmannModeExponent hbar omega eta energyGap * (t : ℂ))

/-- Every single Lehmann mode is integrable on the causal half-line for `eta > 0`. -/
theorem integrableOn_lehmannMode_Ioi_zero
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    IntegrableOn (lehmannMode hbar omega eta energyGap) (Ioi 0) volume := by
  unfold lehmannMode
  apply integrableOn_exp_mul_complex_Ioi
  simpa using neg_lt_zero.mpr heta

/-- The causal half-line integral of one damped transition mode. -/
theorem integral_lehmannMode_Ioi_zero
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    (∫ t : ℝ in Ioi 0, lehmannMode hbar omega eta energyGap t) =
      -1 / lehmannModeExponent hbar omega eta energyGap := by
  unfold lehmannMode
  simpa using integral_exp_mul_complex_Ioi
    (a := lehmannModeExponent hbar omega eta energyGap)
    (by simpa using neg_lt_zero.mpr heta) 0

/-- The same integral written in the conventional resolvent denominator form. -/
theorem integral_lehmannMode_Ioi_zero_eq_resolvent
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    (∫ t : ℝ in Ioi 0, lehmannMode hbar omega eta energyGap t) =
      1 / ((eta : ℂ) - Complex.I * ((omega + energyGap / hbar : ℝ) : ℂ)) := by
  rw [integral_lehmannMode_Ioi_zero hbar omega eta energyGap heta]
  simp [lehmannModeExponent]

/-- One scalar term in a finite Lehmann representation. -/
noncomputable def lehmannTerm
    (hbar omega eta energyGap : ℝ) (weight : ℂ) : ℂ :=
  weight / ((eta : ℂ) - Complex.I * ((omega + energyGap / hbar : ℝ) : ℂ))

/-- A finite spectral sum of Lehmann transition terms. -/
noncomputable def finiteLehmannSum
    {ι : Type*} (s : Finset ι)
    (hbar omega eta : ℝ) (energyGap : ι → ℝ) (weight : ι → ℂ) : ℂ :=
  ∑ j ∈ s, lehmannTerm hbar omega eta (energyGap j) (weight j)

end
end LinearResponse
end QuantumTheory
