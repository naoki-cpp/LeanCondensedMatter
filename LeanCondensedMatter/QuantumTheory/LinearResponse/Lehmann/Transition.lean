import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.Module

set_option linter.style.header false

/-! # Scalar Lehmann transitions and analytic estimates -/

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
is the physical coefficient `(i / ℏ)(pₘ-pₙ)AₘₙBₙₘ`.  The `hbar` type index ties that weight to
the same reduced Planck constant used by the time phase and frequency denominator, so later
representations cannot mix conventions accidentally. -/
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

/-- The conventional fixed-rate Lehmann resolvent denominator. -/
noncomputable def lehmannDenominator
    (hbar omega eta energyGap : ℝ) : ℂ :=
  (eta : ℂ) - Complex.I * ((omega + energyGap / hbar : ℝ) : ℂ)

@[simp]
theorem lehmannDenominator_re
    (hbar omega eta energyGap : ℝ) :
    (lehmannDenominator hbar omega eta energyGap).re = eta := by
  simp [lehmannDenominator]

/-- A single causal Lehmann transition mode. -/
noncomputable def lehmannMode
    (hbar omega eta energyGap : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-lehmannDenominator hbar omega eta energyGap * (t : ℂ))

/-- Every single Lehmann mode is integrable on the causal half-line for `eta > 0`. -/
theorem integrableOn_lehmannMode_Ioi_zero
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    IntegrableOn (lehmannMode hbar omega eta energyGap) (Ioi 0) volume := by
  unfold lehmannMode
  apply integrableOn_exp_mul_complex_Ioi
  simpa using neg_lt_zero.mpr heta

/-- A nonzero switching rate makes every scalar Lehmann denominator nonzero. -/
theorem lehmannDenominator_ne_zero
    (hbar omega eta energyGap : ℝ) (heta : eta ≠ 0) :
    lehmannDenominator hbar omega eta energyGap ≠ 0 := by
  intro hzero
  have hre : eta = 0 := by
    simpa [lehmannDenominator] using congrArg Complex.re hzero
  exact heta hre

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

/-- The mode integral written in conventional resolvent-denominator form. -/
theorem integral_lehmannMode_Ioi_zero_eq_resolvent
    (hbar omega eta energyGap : ℝ) (heta : 0 < eta) :
    (∫ t : ℝ in Ioi 0, lehmannMode hbar omega eta energyGap t) =
      (lehmannDenominator hbar omega eta energyGap)⁻¹ := by
  unfold lehmannMode
  simpa using integral_exp_mul_complex_Ioi
    (a := -lehmannDenominator hbar omega eta energyGap)
    (by simpa using neg_lt_zero.mpr heta) 0

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


end
end LinearResponse
end QuantumTheory
