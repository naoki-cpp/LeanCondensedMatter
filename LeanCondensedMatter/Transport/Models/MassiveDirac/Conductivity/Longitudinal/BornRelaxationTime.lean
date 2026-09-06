import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.RelaxationTime
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.TransportRate
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Microscopic Born specialization of the longitudinal RTA benchmark

This module is the conductivity-level bridge from the microscopic scalar-disorder Born transport
lifetime to the already-owned zero-temperature relaxation-time benchmark.  It introduces no second
conductivity definition: the existing `zeroTemperatureRelaxationTimeLongitudinalConductivity` is
evaluated directly on `continuumBornUpperBandPositiveTransportLifetime`.

For fixed positive disorder strength `W`, the resulting benchmark is

```text
σxx^(Born-RTA) = e² ℏ v² (εF² - m²) / [π W (εF² + 3 m²)].
```

Thus the raw weak-disorder conductivity has the expected `1/W` Drude scaling.  The finite quantity
for comparison with a later controlled Středa weak-disorder theorem is `W * σxx`, not a finite
`W → 0⁺` limit of `σxx` itself.

No Kubo/Středa broadening limit, exact disorder average, SCBA/Ward statement, crossed diagram, or
ultraviolet/thermodynamic limit is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

private theorem continuumBornUpperBandTransportLifetime_eq_closed
    (v m fermiEnergy disorderStrength hbar : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0) (hdisorder : disorderStrength ≠ 0)
    (hfermiEnergy : fermiEnergy ≠ 0) :
    continuumBornUpperBandTransportLifetime
        v m fermiEnergy disorderStrength hbar =
      4 * hbar ^ 3 * v ^ 2 * fermiEnergy /
        (disorderStrength * (fermiEnergy ^ 2 + 3 * m ^ 2)) := by
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_ne_zero hfermiEnergy
  have hsum : fermiEnergy ^ 2 + 3 * m ^ 2 ≠ 0 :=
    ne_of_gt
      (add_pos_of_pos_of_nonneg hfermiSq
        (mul_nonneg (by norm_num) (sq_nonneg m)))
  unfold continuumBornUpperBandTransportLifetime
  rw [continuumBornUpperBandTransportScatteringRate_eq
    v m fermiEnergy disorderStrength hbar hvelocity hhbar hfermiEnergy]
  field_simp [hvelocity, hhbar, hdisorder, hfermiEnergy, hsum]

/-- The zero-temperature massive-Dirac RTA benchmark evaluated on the microscopic Born transport
lifetime has the explicit `1/W` form

`σxx = e² ℏ v² (εF² - m²) / [π W (εF² + 3 m²)]`.

The positivity assumptions are exactly those used to package the microscopic lifetime as a
`PositiveTransportLifetime`; no finite clean-disorder limit is asserted. -/
theorem zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq
    (e hbar v m fermiEnergy disorderStrength : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hmF : |m| < fermiEnergy) :
    zeroTemperatureRelaxationTimeLongitudinalConductivity
        e hbar v m fermiEnergy
        (continuumBornUpperBandPositiveTransportLifetime
          v m fermiEnergy disorderStrength hbar
          hvelocity hhbar hdisorder hmF) =
      e ^ 2 * hbar * v ^ 2 * (fermiEnergy ^ 2 - m ^ 2) /
        (Real.pi * disorderStrength * (fermiEnergy ^ 2 + 3 * m ^ 2)) := by
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hhbarNe : hbar ≠ 0 := ne_of_gt hhbar
  have hdisorderNe : disorderStrength ≠ 0 := ne_of_gt hdisorder
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_ne_zero hfermiNe
  have hsum : fermiEnergy ^ 2 + 3 * m ^ 2 ≠ 0 :=
    ne_of_gt
      (add_pos_of_pos_of_nonneg hfermiSq
        (mul_nonneg (by norm_num) (sq_nonneg m)))
  rw [zeroTemperatureRelaxationTimeLongitudinalConductivity_eq
    e hbar v m fermiEnergy
    (continuumBornUpperBandPositiveTransportLifetime
      v m fermiEnergy disorderStrength hbar
      hvelocity hhbar hdisorder hmF)
    hhbarNe hvelocity hmF]
  simp only [continuumBornUpperBandPositiveTransportLifetime]
  rw [continuumBornUpperBandTransportLifetime_eq_closed
    v m fermiEnergy disorderStrength hbar
    hvelocity hhbarNe hdisorderNe hfermiNe]
  field_simp [hhbarNe, hvelocity, hdisorderNe, hfermiNe, hsum, Real.pi_ne_zero]

/-- Multiplying the microscopic Born-RTA longitudinal conductivity by the disorder strength removes
the Drude `1/W` scaling and exposes the finite coefficient that a controlled weak-disorder Středa
calculation should reproduce. -/
theorem disorderStrength_mul_zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq
    (e hbar v m fermiEnergy disorderStrength : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar) (hdisorder : 0 < disorderStrength)
    (hmF : |m| < fermiEnergy) :
    disorderStrength *
        zeroTemperatureRelaxationTimeLongitudinalConductivity
          e hbar v m fermiEnergy
          (continuumBornUpperBandPositiveTransportLifetime
            v m fermiEnergy disorderStrength hbar
            hvelocity hhbar hdisorder hmF) =
      e ^ 2 * hbar * v ^ 2 * (fermiEnergy ^ 2 - m ^ 2) /
        (Real.pi * (fermiEnergy ^ 2 + 3 * m ^ 2)) := by
  rw [zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq
    e hbar v m fermiEnergy disorderStrength hvelocity hhbar hdisorder hmF]
  have hdisorderNe : disorderStrength ≠ 0 := ne_of_gt hdisorder
  have hfermiPos : 0 < fermiEnergy := lt_of_le_of_lt (abs_nonneg m) hmF
  have hfermiNe : fermiEnergy ≠ 0 := ne_of_gt hfermiPos
  have hfermiSq : 0 < fermiEnergy ^ 2 := sq_pos_of_ne_zero hfermiNe
  have hsum : fermiEnergy ^ 2 + 3 * m ^ 2 ≠ 0 :=
    ne_of_gt
      (add_pos_of_pos_of_nonneg hfermiSq
        (mul_nonneg (by norm_num) (sq_nonneg m)))
  field_simp [hdisorderNe, hsum, Real.pi_ne_zero]

end

end QuantumTheory.Transport.Models.MassiveDirac
