import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticIntegrability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-!
# Pure-point Lehmann representation

This module owns the scalar ordered-transition conventions used throughout the pure-point Lehmann
path. For an ordered transition `(m,n)`, the canonical orientation is

```text
ΔEₘₙ = Eₘ - Eₙ,
Δpₘₙ = pₘ - pₙ,
Wₘₙ = (i / ℏ) Δpₘₙ Aₘₙ Bₙₘ.
```

`orderedLehmannEnergyGap`, `orderedLehmannProbabilityDifference`, and
`orderedLehmannTransitionWeight` are the single scalar helpers for these conventions. The time
phase and fixed-rate denominator consume the same ordered gap. With
`A_I(t) = U₀(-t) A U₀(t)` and Fourier phase `exp (+i ω t)`, one transition contributes

`exp (i ΔEₘₙ t / ℏ)`

in the time domain and

`1 / (η - i (ω + ΔEₘₙ / ℏ))`

in the fixed-rate frequency domain.

The main pure-point API is not finite-dimensional. `PurePointLehmannData` packages a Hilbert basis
of energy eigenvectors and normalized diagonal probabilities, while `PurePointLehmannSummable`
records the absolute summability needed for the countable double transition series. In finite
dimension that condition is automatic. Proving it from bounded observables and a trace-class
diagonal state in infinite dimension is kept as a separate theorem layer.

The switching-rate limit `η → 0⁺` is intentionally not formed here.
-/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

/-- Canonical energy gap of an ordered Lehmann transition `(m,n)`. -/
def orderedLehmannEnergyGap (energyM energyN : ℝ) : ℝ :=
  energyM - energyN

/-- Canonical diagonal-probability difference of an ordered Lehmann transition `(m,n)`. -/
def orderedLehmannProbabilityDifference
    (probabilityM probabilityN : ℝ) : ℝ :=
  probabilityM - probabilityN

/-- Canonical physical weight of an ordered Lehmann transition `(m,n)`.

The matrix elements are supplied in the orientation `Aₘₙ` and `Bₙₘ`. -/
noncomputable def orderedLehmannTransitionWeight
    (hbar probabilityM probabilityN : ℝ)
    (matrixAMN matrixBNM : ℂ) : ℂ :=
  (Complex.I / (hbar : ℂ)) *
    (orderedLehmannProbabilityDifference probabilityM probabilityN : ℂ) *
    matrixAMN * matrixBNM

@[simp]
theorem orderedLehmannEnergyGap_eq
    (energyM energyN : ℝ) :
    orderedLehmannEnergyGap energyM energyN = energyM - energyN := rfl

@[simp]
theorem orderedLehmannProbabilityDifference_eq
    (probabilityM probabilityN : ℝ) :
    orderedLehmannProbabilityDifference probabilityM probabilityN =
      probabilityM - probabilityN := rfl

/-- Equal diagonal probabilities force the canonical physical transition weight to vanish. -/
@[simp]
theorem orderedLehmannTransitionWeight_sameProbability
    (hbar probability : ℝ) (matrixAMN matrixBNM : ℂ) :
    orderedLehmannTransitionWeight hbar probability probability
      matrixAMN matrixBNM = 0 := by
  simp [orderedLehmannTransitionWeight]

/-- Heisenberg time phase associated with one ordered Lehmann energy gap. -/
noncomputable def lehmannTimePhase
    (hbar energyGap t : ℝ) : ℂ :=
  Complex.exp
    (Complex.I * ((((energyGap * t) / hbar : ℝ) : ℂ)))

@[simp]
theorem norm_lehmannTimePhase
    (hbar energyGap t : ℝ) :
    ‖lehmannTimePhase hbar energyGap t‖ = 1 := by
  rw [lehmannTimePhase, Complex.norm_exp]
  simp

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

/-- The conventional fixed-rate Lehmann resolvent denominator. -/
noncomputable def lehmannDenominator
    (hbar omega eta energyGap : ℝ) : ℂ :=
  (eta : ℂ) - Complex.I * ((omega + energyGap / hbar : ℝ) : ℂ)

@[simp]
theorem lehmannDenominator_re
    (hbar omega eta energyGap : ℝ) :
    (lehmannDenominator hbar omega eta energyGap).re = eta := by
  simp [lehmannDenominator]

/-- The switching rate is a lower bound for the norm of every Lehmann denominator. -/
theorem eta_le_norm_lehmannDenominator
    (hbar omega eta energyGap : ℝ) :
    eta ≤ ‖lehmannDenominator hbar omega eta energyGap‖ := by
  simpa using RCLike.re_le_norm (lehmannDenominator hbar omega eta energyGap)

/-- At positive switching rate, the inverse denominator is uniformly bounded by `1 / eta`. -/
theorem norm_inv_lehmannDenominator_le
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    ‖(lehmannDenominator hbar omega eta energyGap)⁻¹‖ ≤ 1 / eta := by
  rw [norm_inv]
  simpa [one_div] using one_div_le_one_div_of_le heta
    (eta_le_norm_lehmannDenominator hbar omega eta energyGap)

/-- The denominator is the negative of the corresponding damped-mode exponent. -/
theorem lehmannDenominator_eq_neg_exponent
    (hbar omega eta energyGap : ℝ) :
    lehmannDenominator hbar omega eta energyGap =
      -lehmannModeExponent hbar omega eta energyGap := by
  unfold lehmannModeExponent lehmannDenominator
  ring

/-- The mode integral written in conventional resolvent-denominator form. -/
theorem integral_lehmannMode_Ioi_zero_eq_resolvent
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    (∫ t : ℝ in Ioi 0, lehmannMode hbar omega eta energyGap t) =
      (lehmannDenominator hbar omega eta energyGap)⁻¹ := by
  rw [integral_lehmannMode_Ioi_zero hbar omega eta energyGap heta]
  rw [lehmannDenominator_eq_neg_exponent]
  simp [div_eq_mul_inv]

/-- One scalar term in a Lehmann representation. -/
noncomputable def lehmannTerm
    (hbar omega eta energyGap : ℝ) (weight : ℂ) : ℂ :=
  weight * (lehmannDenominator hbar omega eta energyGap)⁻¹

/-- Uniform comparison estimate for a single Lehmann term at positive switching rate. -/
theorem norm_lehmannTerm_le
    (hbar omega eta energyGap : ℝ) (weight : ℂ) (heta : 0 < eta) :
    ‖lehmannTerm hbar omega eta energyGap weight‖ ≤
      (1 / eta) * ‖weight‖ := by
  unfold lehmannTerm
  rw [norm_mul]
  calc
    ‖weight‖ * ‖(lehmannDenominator hbar omega eta energyGap)⁻¹‖ ≤
        ‖weight‖ * (1 / eta) :=
      mul_le_mul_of_nonneg_left
        (norm_inv_lehmannDenominator_le hbar omega eta energyGap heta)
        (norm_nonneg weight)
    _ = (1 / eta) * ‖weight‖ := by ring

/-- An absolutely summable family of transition weights produces a summable Lehmann series at
any strictly positive switching rate. -/
theorem summable_lehmannTerm_of_pos
    {κ : Type*} (hbar omega eta : ℝ)
    (energyGap : κ → ℝ) (weight : κ → ℂ)
    (hweight : Summable fun j => ‖weight j‖) (heta : 0 < eta) :
    Summable fun j => lehmannTerm hbar omega eta (energyGap j) (weight j) := by
  apply (hweight.mul_left (1 / eta)).of_norm_bounded
  intro j
  exact norm_lehmannTerm_le hbar omega eta (energyGap j) (weight j) heta

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pure-point spectral data for a bounded free system and a diagonal normalized state.

The basis vectors diagonalize `system.hamiltonian`; `probability` gives the corresponding diagonal
state weights. The index type may be infinite. -/
structure PurePointLehmannData
    (system : BoundedFreeSystem H) (ι : Type*) where
  /-- Hilbert basis of energy eigenvectors. -/
  basis : HilbertBasis ι ℂ H
  /-- Energy assigned to each basis vector. -/
  energy : ι → ℝ
  hamiltonian_apply_basis : ∀ i,
    system.hamiltonian.1 (basis i) = (energy i : ℂ) • basis i
  /-- Normalized diagonal probability assigned to each basis vector. -/
  probability : ι → ℝ
  probability_nonneg : ∀ i, 0 ≤ probability i
  probability_summable : Summable probability
  probability_tsum : ∑' i, probability i = 1

variable {ι : Type*} (system : BoundedFreeSystem H)

/-- Canonical ordered energy gap of one pure-point transition `(m,n)`. -/
def purePointTransitionEnergyGap
    (data : PurePointLehmannData system ι) (mn : ι × ι) : ℝ :=
  orderedLehmannEnergyGap (data.energy mn.1) (data.energy mn.2)

@[simp]
theorem purePointTransitionEnergyGap_eq
    (data : PurePointLehmannData system ι) (mn : ι × ι) :
    purePointTransitionEnergyGap system data mn =
      data.energy mn.1 - data.energy mn.2 := rfl

/-- The physical spectral weight
`(i / ℏ) (pₘ - pₙ) Aₘₙ Bₙₘ` of one pure-point transition. -/
noncomputable def purePointTransitionWeight
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : ℂ :=
  orderedLehmannTransitionWeight system.hbar
    (data.probability mn.1) (data.probability mn.2)
    (inner ℂ (data.basis mn.1) (A (data.basis mn.2)))
    (inner ℂ (data.basis mn.2) (B (data.basis mn.1)))

/-- Diagonal pure-point transitions have zero physical weight. -/
@[simp]
theorem purePointTransitionWeight_diag
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (i : ι) :
    purePointTransitionWeight system data A B (i, i) = 0 := by
  simp [purePointTransitionWeight]

/-- Absolute-summability condition for the countable pure-point transition weights. -/
def PurePointLehmannSummable
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  Summable fun mn : ι × ι => ‖purePointTransitionWeight system data A B mn‖

/-- The fixed-positive-rate pure-point Lehmann series. -/
noncomputable def purePointLehmannSeries
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : ℂ :=
  ∑' mn : ι × ι,
    lehmannTerm system.hbar omega eta
      (purePointTransitionEnergyGap system data mn)
      (purePointTransitionWeight system data A B mn)

/-- Absolute transition-weight summability implies summability of the fixed-rate pure-point
Lehmann series for every `eta > 0`. -/
theorem summable_purePointLehmannSeries_of_pos
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ)
    (hsum : PurePointLehmannSummable system data A B) (heta : 0 < eta) :
    Summable fun mn : ι × ι =>
      lehmannTerm system.hbar omega eta
        (data.energy mn.1 - data.energy mn.2)
        (purePointTransitionWeight system data A B mn) := by
  simpa using
    summable_lehmannTerm_of_pos system.hbar omega eta
      (purePointTransitionEnergyGap system data)
      (purePointTransitionWeight system data A B) hsum heta

/-- In finite dimension, the absolute transition-weight condition is automatic. -/
theorem purePointLehmannSummable_of_finite
    [Finite ι] (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) :
    PurePointLehmannSummable system data A B := by
  exact Summable.of_finite

/-- For a finite spectral index, the countable-series definition reduces to the usual finite
double sum. -/
theorem purePointLehmannSeries_eq_finite_sum
    [Fintype ι] (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    purePointLehmannSeries system data A B omega eta =
      ∑ mn : ι × ι,
        lehmannTerm system.hbar omega eta
          (data.energy mn.1 - data.energy mn.2)
          (purePointTransitionWeight system data A B mn) := by
  simp [purePointLehmannSeries]

end
end LinearResponse
end QuantumTheory
