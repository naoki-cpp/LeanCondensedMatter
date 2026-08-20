import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperatureSharpRadial
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fermi-radius uniqueness for the zero-temperature massive-Dirac Bastin limit

The sharp zero-temperature radial profile introduced after the occupation-weighted dominated-
convergence theorem agrees with the exact half-weight target once the radial Fermi-surface locus is
contained in one point. This file discharges that model-specific hypothesis for the massive-Dirac
dispersion.

On the nonnegative radial axis,

```text
E(p) = sqrt(v² p² + m²)
```

is injective whenever `v ≠ 0`. Consequently either band energy has at most one radial solution of
`E_band(p) = ε_F`. No positivity assumption on `m` is needed for this uniqueness statement; the
only degenerate case excluded here is `v = 0`, where the dispersion is momentum independent.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Set

/-- The positive massive-Dirac radial energy is injective on nonnegative momentum when `v ≠ 0`. -/
theorem energy_radial_eq_imp_eq_of_nonneg
    (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (henergy : energy v m p 0 = energy v m q 0) :
    p = q := by
  have hsquare := congrArg (fun x : ℝ => x ^ 2) henergy
  rw [energy_sq v m p 0, energy_sq v m q 0] at hsquare
  unfold energySq at hsquare
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  nlinarith

/-- Either massive-Dirac band energy is injective on the nonnegative radial axis when `v ≠ 0`. -/
theorem bandEnergy_radial_eq_imp_eq_of_nonneg
    (band : Band) (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (henergy : bandEnergy band v m p 0 = bandEnergy band v m q 0) :
    p = q := by
  apply energy_radial_eq_imp_eq_of_nonneg v m p q hv hp hq
  cases band <;> simpa [bandEnergy] using henergy

/-- A specified nonnegative Fermi radius is the unique radial Fermi-surface point in every finite
cutoff interval. This discharges the abstract uniqueness hypothesis of the preceding sharp-profile
theorem for the concrete massive-Dirac dispersion. -/
theorem finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_eq_sharp_of_fermiRadius
    (band : Band) (e v m fermiEnergy pMax pF : ℝ)
    (hv : v ≠ 0) (hpF : 0 ≤ pF)
    (hfermiF : bandEnergy band v m pF 0 = fermiEnergy) :
    finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
        band e v m fermiEnergy pMax =
      finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        band e v m fermiEnergy pMax := by
  apply finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_eq_sharp_of_fermi_unique
    band e v m fermiEnergy pMax pF
  intro p hp hfermi
  apply bandEnergy_radial_eq_imp_eq_of_nonneg band v m p pF hv hp.1 hpF
  exact hfermi.trans hfermiF.symm

end

end AnomalousHall.MassiveDirac
