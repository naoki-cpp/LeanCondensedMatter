import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperatureFermiRadius
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Explicit metallic Fermi radius for the zero-temperature massive-Dirac Bastin limit

The preceding slice proves that the radial massive-Dirac dispersion has at most one Fermi radius
on the nonnegative momentum axis when `v ≠ 0`. This file constructs that radius explicitly in the
positive-mass metallic regime and turns the abstract uniqueness bridge into concrete upper- and
lower-band occupation statements.

For `0 < m ≤ ε_F` and `v ≠ 0`, define

```text
p_F = sqrt(ε_F² - m²) / |v|.
```

Then `E(p_F) = ε_F`, the upper band is occupied exactly for `p < p_F`, and the lower band is occupied
at every radial momentum. No radial integration or ultraviolet limit is performed here; those are
left to the following sharp-shell bridge.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Set

/-- Metallic upper-band Fermi radius for the massive-Dirac dispersion. -/
def metallicFermiRadius (v m fermiEnergy : ℝ) : ℝ :=
  Real.sqrt (fermiEnergy ^ 2 - m ^ 2) / |v|

/-- The metallic Fermi radius is nonnegative. -/
theorem metallicFermiRadius_nonneg
    (v m fermiEnergy : ℝ) (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    0 ≤ metallicFermiRadius v m fermiEnergy := by
  unfold metallicFermiRadius
  have hrad : 0 ≤ fermiEnergy ^ 2 - m ^ 2 := by
    nlinarith [sq_nonneg (fermiEnergy - m)]
  exact div_nonneg (Real.sqrt_nonneg _) (abs_nonneg v)

/-- Squaring the explicit metallic Fermi radius removes the square root and absolute value. -/
theorem metallicFermiRadius_sq
    (v m fermiEnergy : ℝ)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    metallicFermiRadius v m fermiEnergy ^ 2 =
      (fermiEnergy ^ 2 - m ^ 2) / v ^ 2 := by
  unfold metallicFermiRadius
  have hrad : 0 ≤ fermiEnergy ^ 2 - m ^ 2 := by
    nlinarith [sq_nonneg (fermiEnergy - m)]
  rw [div_pow, Real.sq_sqrt hrad]
  simp [sq_abs]

/-- The positive Dirac energy at the metallic Fermi radius is exactly `ε_F`. -/
theorem energy_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    energy v m (metallicFermiRadius v m fermiEnergy) 0 = fermiEnergy := by
  have hfermiNonneg : 0 ≤ fermiEnergy := le_trans (le_of_lt hm) hmF
  have hsq :
      energy v m (metallicFermiRadius v m fermiEnergy) 0 ^ 2 =
        fermiEnergy ^ 2 := by
    rw [energy_sq]
    unfold energySq
    norm_num
    rw [metallicFermiRadius_sq v m fermiEnergy hm hmF]
    field_simp [pow_ne_zero 2 hv]
    ring
  have henergyNonneg :
      0 ≤ energy v m (metallicFermiRadius v m fermiEnergy) 0 :=
    Real.sqrt_nonneg _
  nlinarith

/-- The upper-band energy at the explicit metallic Fermi radius is exactly `ε_F`. -/
theorem bandEnergy_upper_metallicFermiRadius
    (v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    bandEnergy .upper v m (metallicFermiRadius v m fermiEnergy) 0 = fermiEnergy := by
  simpa using energy_metallicFermiRadius v m fermiEnergy hv hm hmF

/-- Positive radial energy is strictly increasing on the nonnegative axis when `v ≠ 0`. -/
theorem energy_radial_lt_of_lt_of_nonneg
    (v m p q : ℝ) (hv : v ≠ 0) (hp : 0 ≤ p) (hpq : p < q) :
    energy v m p 0 < energy v m q 0 := by
  have hq : 0 ≤ q := hp.trans (le_of_lt hpq)
  have hvSq : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hpSqLt : p ^ 2 < q ^ 2 := by
    nlinarith
  have henergySqLt : energy v m p 0 ^ 2 < energy v m q 0 ^ 2 := by
    rw [energy_sq, energy_sq]
    unfold energySq
    norm_num
    nlinarith
  have hpEnergy : 0 ≤ energy v m p 0 := Real.sqrt_nonneg _
  have hqEnergy : 0 ≤ energy v m q 0 := Real.sqrt_nonneg _
  nlinarith

/-- In the metallic regime the upper band is occupied exactly below the explicit Fermi radius. -/
theorem bandEnergy_upper_lt_fermi_iff_lt_metallicFermiRadius
    (v m fermiEnergy p : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) (hp : 0 ≤ p) :
    bandEnergy .upper v m p 0 < fermiEnergy ↔
      p < metallicFermiRadius v m fermiEnergy := by
  rw [bandEnergy_upper]
  have hfermi := energy_metallicFermiRadius v m fermiEnergy hv hm hmF
  constructor
  · intro henergy
    by_contra hpF
    have hpFle : metallicFermiRadius v m fermiEnergy ≤ p := le_of_not_gt hpF
    rcases hpFle.eq_or_lt with hpEq | hpLt
    · have hfermi' := hfermi
      rw [hpEq] at hfermi'
      linarith
    · have hmono := energy_radial_lt_of_lt_of_nonneg
        v m (metallicFermiRadius v m fermiEnergy) p hv
        (metallicFermiRadius_nonneg v m fermiEnergy hm hmF) hpLt
      linarith
  · intro hpLt
    have hmono := energy_radial_lt_of_lt_of_nonneg
      v m p (metallicFermiRadius v m fermiEnergy) hv hp hpLt
    rw [hfermi] at hmono
    exact hmono

/-- In the positive-mass metallic regime the lower band is occupied at every radial momentum. -/
theorem bandEnergy_lower_lt_fermi
    (v m fermiEnergy p : ℝ) (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    bandEnergy .lower v m p 0 < fermiEnergy := by
  rw [bandEnergy_lower]
  have henergy : 0 ≤ energy v m p 0 := Real.sqrt_nonneg _
  have hfermi : 0 < fermiEnergy := lt_of_lt_of_le hm hmF
  linarith

/-- The exact zero-temperature upper-band target and its sharp profile have the same finite radial
integral with the explicit metallic Fermi radius, so no abstract uniqueness hypothesis remains. -/
theorem finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_upper_eq_sharp_metallic
    (e v m fermiEnergy pMax : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
        .upper e v m fermiEnergy pMax =
      finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .upper e v m fermiEnergy pMax := by
  exact finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_eq_sharp_of_fermiRadius
    .upper e v m fermiEnergy pMax (metallicFermiRadius v m fermiEnergy)
    hv (metallicFermiRadius_nonneg v m fermiEnergy hm hmF)
    (bandEnergy_upper_metallicFermiRadius v m fermiEnergy hv hm hmF)

/-- The exact zero-temperature lower-band target also equals its sharp profile in the metallic
regime: a lower-band state cannot lie on a positive Fermi surface. -/
theorem finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_lower_eq_sharp_metallic
    (e v m fermiEnergy pMax : ℝ)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
        .lower e v m fermiEnergy pMax =
      finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .lower e v m fermiEnergy pMax := by
  apply finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_eq_sharp_of_fermi_unique
    .lower e v m fermiEnergy pMax 0
  intro p _ hfermi
  have hoccupied := bandEnergy_lower_lt_fermi v m fermiEnergy p hm hmF
  rw [hfermi] at hoccupied
  exact (lt_irrefl _ hoccupied).elim

end

end AnomalousHall.MassiveDirac
