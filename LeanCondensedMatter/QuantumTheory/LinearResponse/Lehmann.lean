import LeanCondensedMatter.QuantumTheory.LinearResponse.AdiabaticIntegrability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-!
# Pure-point Lehmann representation

This module separates the scalar analytic denominator from the spectral data entering a Lehmann
representation. With the repository conventions

`A_I(t) = U₀(-t) A U₀(t)` and Fourier phase `exp (+i ω t)`,

a transition with energy gap `ΔE = Eₘ - Eₙ` contributes

`exp ((-η + i (ω + ΔE / ℏ)) t)`.

For every `η > 0`, its causal half-line integral is

`1 / (η - i (ω + ΔE / ℏ))`.

`LehmannTransitionData` is the canonical ordered-transition seam.  Its constructor
`orderedLehmannTransitionData` fixes both `ΔE = Eₘ - Eₙ` and
`Wₘₙ = (i / ℏ)(pₘ-pₙ)AₘₙBₙₘ`; time-domain, frequency-domain, pure-point, and finite-table
consumers project from that same pair rather than reconstructing it independently.

The main API is not finite-dimensional. `PurePointLehmannData` packages a Hilbert basis of energy
eigenvectors and normalized diagonal probabilities, while `PurePointLehmannSummable` records the
absolute summability needed for the countable double transition series. In finite dimension that
condition is automatic. Proving it from bounded observables and a trace-class diagonal state in
infinite dimension is kept as a separate theorem layer.

The switching-rate limit `η → 0⁺` is intentionally not formed here.
-/

namespace QuantumTheory
namespace LinearResponse

open Set MeasureTheory

noncomputable section

/-- Canonical energy gap of an ordered Lehmann transition `(m,n)`. -/
@[simp]
abbrev orderedLehmannEnergyGap (energyM energyN : ℝ) : ℝ :=
  energyM - energyN

/-- Canonical physical weight `(i/ℏ)(pₘ-pₙ)AₘₙBₙₘ` of an ordered Lehmann transition. -/
@[simp]
noncomputable abbrev orderedLehmannTransitionWeight
    (hbar probabilityM probabilityN : ℝ) (matrixAMN matrixBNM : ℂ) : ℂ :=
  (Complex.I / (hbar : ℂ)) *
    ((probabilityM - probabilityN : ℝ) : ℂ) * matrixAMN * matrixBNM

/-- Canonical scalar data for one ordered Lehmann transition.

The orientation is always the ordered pair `(m,n)`: `energyGap = Eₘ - Eₙ`, while `weight`
is the physical coefficient `(i / ℏ)(pₘ-pₙ)AₘₙBₙₘ`.  All later representations should adapt to
this pair rather than choose their own sign or index convention. -/
structure LehmannTransitionData (hbar : ℝ) where
  /-- Ordered energy gap `Eₘ - Eₙ`. -/
  energyGap : ℝ
  /-- Physical transition weight `(i / ℏ)(pₘ-pₙ)AₘₙBₙₘ`. -/
  weight : ℂ

/-- Build the canonical transition data from ordered spectral entries. -/
noncomputable def orderedLehmannTransitionData
    (hbar energyM energyN probabilityM probabilityN : ℝ)
    (matrixAMN matrixBNM : ℂ) : LehmannTransitionData hbar where
  energyGap := orderedLehmannEnergyGap energyM energyN
  weight := orderedLehmannTransitionWeight hbar probabilityM probabilityN matrixAMN matrixBNM

@[simp]
theorem orderedLehmannTransitionData_energyGap
    (hbar energyM energyN probabilityM probabilityN : ℝ)
    (matrixAMN matrixBNM : ℂ) :
    (orderedLehmannTransitionData hbar energyM energyN probabilityM probabilityN
      matrixAMN matrixBNM).energyGap =
      orderedLehmannEnergyGap energyM energyN := rfl

@[simp]
theorem orderedLehmannTransitionData_weight
    (hbar energyM energyN probabilityM probabilityN : ℝ)
    (matrixAMN matrixBNM : ℂ) :
    (orderedLehmannTransitionData hbar energyM energyN probabilityM probabilityN
      matrixAMN matrixBNM).weight =
      orderedLehmannTransitionWeight hbar probabilityM probabilityN matrixAMN matrixBNM := rfl

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

namespace LehmannTransitionData

/-- Time-domain contribution of one canonical transition. -/
noncomputable def timeTerm
    {hbar : ℝ} (transition : LehmannTransitionData hbar) (t : ℝ) : ℂ :=
  transition.weight *
    Complex.exp
      (Complex.I * ((((transition.energyGap * t) / hbar : ℝ) : ℂ)))

/-- The pure phase in a canonical time-domain transition does not change its norm. -/
@[simp]
theorem norm_timeTerm
    {hbar : ℝ} (transition : LehmannTransitionData hbar) (t : ℝ) :
    ‖transition.timeTerm t‖ = ‖transition.weight‖ := by
  rw [timeTerm, norm_mul, Complex.norm_exp]
  simp

/-- Fixed-rate frequency-domain contribution of one canonical transition. -/
noncomputable def frequencyTerm
    {hbar : ℝ} (transition : LehmannTransitionData hbar) (omega eta : ℝ) : ℂ :=
  lehmannTerm hbar omega eta transition.energyGap transition.weight

end LehmannTransitionData

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

/-- An absolutely summable family of canonical transition weights produces a summable
fixed-rate frequency series at any strictly positive switching rate. -/
theorem LehmannTransitionData.summable_frequencyTerm_of_pos
    {κ : Type*} {hbar : ℝ} (omega eta : ℝ)
    (transition : κ → LehmannTransitionData hbar)
    (hweight : Summable fun j => ‖(transition j).weight‖) (heta : 0 < eta) :
    Summable fun j => (transition j).frequencyTerm omega eta := by
  apply (hweight.mul_left (1 / eta)).of_norm_bounded
  intro j
  simpa [LehmannTransitionData.frequencyTerm] using
    norm_lehmannTerm_le hbar omega eta
      (transition j).energyGap (transition j).weight heta

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

/-- Adapt one operator-level ordered pair to the canonical Lehmann transition data. -/
noncomputable def purePointTransitionData
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : LehmannTransitionData system.hbar :=
  orderedLehmannTransitionData system.hbar
    (data.energy mn.1) (data.energy mn.2)
    (data.probability mn.1) (data.probability mn.2)
    (inner ℂ (data.basis mn.1) (A (data.basis mn.2)))
    (inner ℂ (data.basis mn.2) (B (data.basis mn.1)))

/-- The physical spectral weight
`(i / ℏ) (pₘ - pₙ) Aₘₙ Bₙₘ` of one pure-point transition.

This compatibility accessor is the `weight` projection of the canonical transition record. -/
noncomputable def purePointTransitionWeight
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) : ℂ :=
  (purePointTransitionData system data A B mn).weight

@[simp]
theorem purePointTransitionData_energyGap
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (mn : ι × ι) :
    (purePointTransitionData system data A B mn).energyGap =
      orderedLehmannEnergyGap (data.energy mn.1) (data.energy mn.2) := rfl

/-- Diagonal pure-point transitions have zero physical weight. -/
@[simp]
theorem purePointTransitionWeight_diag
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (i : ι) :
    purePointTransitionWeight system data A B (i, i) = 0 := by
  simp [purePointTransitionWeight, purePointTransitionData]

/-- Absolute-summability condition for the countable pure-point transition weights. -/
def PurePointLehmannSummable
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) : Prop :=
  Summable fun mn : ι × ι => ‖(purePointTransitionData system data A B mn).weight‖

/-- The fixed-positive-rate pure-point Lehmann series. -/
noncomputable def purePointLehmannSeries
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) : ℂ :=
  ∑' mn : ι × ι,
    (purePointTransitionData system data A B mn).frequencyTerm omega eta

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
  simpa [LehmannTransitionData.frequencyTerm] using
    LehmannTransitionData.summable_frequencyTerm_of_pos
      omega eta (purePointTransitionData system data A B) hsum heta

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
  simp [purePointLehmannSeries, LehmannTransitionData.frequencyTerm]

end
end LinearResponse
end QuantumTheory
