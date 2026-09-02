import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoSiteDimerLehmann

set_option linter.style.header false

/-!
# Closed finite-frequency conductivity of the two-site dimer

This module upgrades the exact unit-dimer benchmark from a single parameter point to a symbolic
fixed-rate formula.  With unit `ℏ` and unit physical volume, write

```text
z = η - iω.
```

For the model-derived two-level Lehmann table, the two off-diagonal transitions combine to

```text
χ_JJ(ω,η) = 4 / (z² + 4).
```

The Peierls contact expectation remains `-1`, while the unit-volume conversion from vector
potential to electric field is `-1 / z`.  Hence, for `η ≠ 0`,

```text
σ(ω,η) = z / (z² + 4).
```

The nonzero-rate assumption is used only to exclude the singular Lehmann/electric-field
denominators when algebraically combining inverse factors.  No `η → 0`, DC, or thermodynamic limit
is taken.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open QuantumTheory.LinearResponse QuantumTheory.Transport
open Transport

noncomputable section

/-- Common complex fixed-rate variable `z = η - iω` for the unit dimer. -/
def twoSiteDimerComplexRate (omega eta : ℝ) : ℂ :=
  (eta : ℂ) - Complex.I * (omega : ℂ)

/-- Denominator `z² + 4` of the closed unit-dimer current response. -/
def twoSiteDimerFrequencyDenominator (omega eta : ℝ) : ℂ :=
  twoSiteDimerComplexRate omega eta ^ 2 + 4

/-- A nonzero switching rate keeps either dimer transition denominator nonzero. -/
theorem twoSiteDimerLehmannDenominator_ne_zero
    (omega eta gap : ℝ) (heta : eta ≠ 0) :
    lehmannDenominator 1 omega eta gap ≠ 0 := by
  intro hzero
  have hre : eta = 0 := by
    simpa [lehmannDenominator] using congrArg Complex.re hzero
  exact heta hre

/-- The closed response denominator factors into the two physical transition denominators. -/
theorem twoSiteDimerFrequencyDenominator_eq_transitionProduct
    (omega eta : ℝ) :
    twoSiteDimerFrequencyDenominator omega eta =
      lehmannDenominator 1 omega eta (-2) *
        lehmannDenominator 1 omega eta 2 := by
  apply Complex.ext <;>
    simp [twoSiteDimerFrequencyDenominator, twoSiteDimerComplexRate,
      lehmannDenominator, pow_two] <;> ring

/-- At nonzero switching rate the closed unit-dimer response denominator is nonsingular. -/
theorem twoSiteDimerFrequencyDenominator_ne_zero
    (omega eta : ℝ) (heta : eta ≠ 0) :
    twoSiteDimerFrequencyDenominator omega eta ≠ 0 := by
  rw [twoSiteDimerFrequencyDenominator_eq_transitionProduct]
  exact mul_ne_zero
    (twoSiteDimerLehmannDenominator_ne_zero omega eta (-2) heta)
    (twoSiteDimerLehmannDenominator_ne_zero omega eta 2 heta)

/-- Closed finite-frequency current-current Lehmann response of the unit-hopping dimer:
`χ_JJ = 4 / ((η - iω)² + 4)` at every nonzero switching rate. -/
theorem twoSiteDimerGroundState_lehmannResponse_frequency
    (omega eta : ℝ) (heta : eta ≠ 0) :
    finiteLehmannTableResponse 1 omega eta twoSiteDimerGroundStateLehmannTable =
      4 * (twoSiteDimerFrequencyDenominator omega eta)⁻¹ := by
  classical
  have hminus := twoSiteDimerLehmannDenominator_ne_zero omega eta (-2) heta
  have hplus := twoSiteDimerLehmannDenominator_ne_zero omega eta 2 heta
  have hgapMinus : ((-1 : ℝ) - 1) = -2 := by norm_num
  have hgapPlus : ((1 : ℝ) + 1) = 2 := by norm_num
  unfold finiteLehmannTableResponse
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue,
    twoSiteDimerGroundStateLehmannTable_energy_zero, sub_neg_eq_add,
    twoSiteDimerGroundStateLehmannTable_energy_one,
    twoSiteDimerGroundStateTransitionWeight_zero_one,
    twoSiteDimerGroundStateTransitionWeight_one_zero,
    finiteLehmannTableTransitionWeight_diag, sub_self]
  simp only [lehmannTerm, zero_mul, zero_add, add_zero]
  rw [hgapMinus, hgapPlus]
  rw [twoSiteDimerFrequencyDenominator_eq_transitionProduct]
  field_simp [hminus, hplus]
  apply Complex.ext
  · simp [lehmannDenominator]
    ring
  · simp [lehmannDenominator]

/-- For unit volume, the electric-field normalization is `-1 / (η - iω)`. -/
theorem twoSiteDimerUnitVolume_normalization_frequency
    (omega eta : ℝ) :
    finiteVolumeConductivityNormalization twoSiteDimerUnitVolume omega eta =
      -(twoSiteDimerComplexRate omega eta)⁻¹ := by
  have hfactor :
      adiabaticElectricFieldFactor omega eta =
        -twoSiteDimerComplexRate omega eta := by
    unfold adiabaticElectricFieldFactor twoSiteDimerComplexRate
    ring
  unfold finiteVolumeConductivityNormalization
  rw [hfactor]
  simp [twoSiteDimerUnitVolume]

/-- A nonzero switching rate keeps `z = η - iω` nonzero. -/
theorem twoSiteDimerComplexRate_ne_zero
    (omega eta : ℝ) (heta : eta ≠ 0) :
    twoSiteDimerComplexRate omega eta ≠ 0 := by
  intro hzero
  have hre : eta = 0 := by
    simpa [twoSiteDimerComplexRate] using congrArg Complex.re hzero
  exact heta hre

/-- Closed unit-volume finite-rate electrical conductivity of the unit-hopping dimer:

`σ(ω,η) = (η - iω) / ((η - iω)² + 4)`.

The proof keeps the Lehmann current response, Peierls contact `-1`, and electric-field
normalization as the existing public definitions and simplifies them only at the final scalar step. -/
theorem twoSiteDimerGroundState_conductivity_frequency
    (omega eta : ℝ) (heta : eta ≠ 0) :
    finiteConductivityTableValue twoSiteDimerUnitVolume 1 omega eta
        twoSiteDimerGroundStateConductivityTable =
      twoSiteDimerComplexRate omega eta *
        (twoSiteDimerFrequencyDenominator omega eta)⁻¹ := by
  have hz := twoSiteDimerComplexRate_ne_zero omega eta heta
  have hden := twoSiteDimerFrequencyDenominator_ne_zero omega eta heta
  unfold finiteConductivityTableValue
  change
    (finiteLehmannTableResponse 1 omega eta twoSiteDimerGroundStateLehmannTable + (-1 : ℂ)) *
        finiteVolumeConductivityNormalization twoSiteDimerUnitVolume omega eta = _
  rw [twoSiteDimerGroundState_lehmannResponse_frequency omega eta heta,
    twoSiteDimerUnitVolume_normalization_frequency]
  field_simp [hz, hden]
  unfold twoSiteDimerFrequencyDenominator
  ring

end
end Validation
end Fermionic
end SecondQuantization
