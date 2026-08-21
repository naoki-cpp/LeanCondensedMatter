import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperatureConductivity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial ultraviolet limit of the zero-temperature massive-Dirac Bastin response

The fixed-radial-cutoff physical Bastin theorem leaves the ultraviolet regulator in the form

```text
Λ(pMax) = E(pMax) = sqrt(v² pMax² + m²).
```

For `v ≠ 0`, this energy cutoff tends to `+∞` with the radial momentum cutoff.  Composing that
fact with the existing clean cutoff theorem closes the iterated clean limit and recovers the
metallic massive-Dirac Hall benchmark.

The positive-broadening limit remains the fixed-cutoff theorem from the preceding file; no
simultaneous `η → 0⁺`, `pMax → ∞` claim is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- On the nonnegative radial axis the Dirac energy dominates the linear kinetic scale `|v| p`. -/
theorem abs_velocity_mul_le_energy_radial
    (v m p : ℝ) (hp : 0 ≤ p) :
    |v| * p ≤ energy v m p 0 := by
  have hleft : 0 ≤ |v| * p := mul_nonneg (abs_nonneg v) hp
  have hright : 0 ≤ energy v m p 0 := Real.sqrt_nonneg _
  have hsq : (|v| * p) ^ 2 ≤ energy v m p 0 ^ 2 := by
    rw [energy_sq]
    unfold energySq
    norm_num
    simp only [mul_pow, sq_abs]
    nlinarith [sq_nonneg m]
  nlinarith

/-- For nonzero Dirac velocity, the positive radial energy tends to `+∞` with momentum. -/
theorem tendsto_energy_radial_atTop
    (v m : ℝ) (hv : v ≠ 0) :
    Tendsto (fun p : ℝ => energy v m p 0) atTop atTop := by
  have hlinear : Tendsto (fun p : ℝ => |v| * p) atTop atTop :=
    Tendsto.const_mul_atTop (abs_pos.mpr hv) tendsto_id
  apply tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with p hp
  exact abs_velocity_mul_le_energy_radial v m p hp

/-- The intrinsic Hall cutoff evaluated at the radial Dirac energy converges to the clean metallic
intrinsic Hall conductivity as `pMax → +∞`. -/
theorem tendsto_intrinsicHallConductivityCutoff_radial_atTop
    (e hbar v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    Tendsto
      (fun pMax : ℝ => intrinsicHallConductivityCutoff
        e hbar m fermiEnergy (energy v m pMax 0))
      atTop
      (nhds (intrinsicHallConductivity e hbar m fermiEnergy)) := by
  exact (tendsto_intrinsicHallConductivityCutoff_atTop
    e hbar m fermiEnergy hm hmF).comp (tendsto_energy_radial_atTop v m hv)

/-- Closed metallic benchmark reached after the radial ultraviolet cutoff is removed,
`σxy = -(e²/2h) (m/εF)`. -/
theorem tendsto_intrinsicHallConductivityCutoff_radial_atTop_massiveDirac
    (e hbar v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hhbar : 0 < hbar) (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    Tendsto
      (fun pMax : ℝ => intrinsicHallConductivityCutoff
        e hbar m fermiEnergy (energy v m pMax 0))
      atTop
      (nhds (-(e ^ 2 / (2 * planckFromReduced hbar)) * (m / fermiEnergy))) := by
  rw [← intrinsicHallConductivity_eq_massiveDirac e hbar m fermiEnergy hhbar
    (lt_of_lt_of_le hm hmF)]
  exact tendsto_intrinsicHallConductivityCutoff_radial_atTop
    e hbar v m fermiEnergy hv hm hmF

end

end AnomalousHall.MassiveDirac
