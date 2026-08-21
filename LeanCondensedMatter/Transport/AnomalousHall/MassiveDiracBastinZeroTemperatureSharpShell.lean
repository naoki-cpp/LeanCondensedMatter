import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperatureMetallicFermiRadius
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinRadialEnergyBridge
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Metallic sharp-shell bridge for the zero-temperature massive-Dirac Bastin limit

The zero-temperature radial dominated-convergence theorem lands on an exact half-weight target.
The preceding slices replace that target by a sharp occupied profile and construct the explicit
metallic Fermi radius

```text
p_F = sqrt(ε_F² - m²) / |v|.
```

This file identifies the resulting sharp lower- and upper-band radial integrals with the clean
radial momentum integrals and then with the existing positive-energy shell integrals.  Thus the
physical zero-temperature finite-radial Bastin limit is connected to the already-normalized clean
finite-cutoff benchmark without mixing the radial broadening limit with the ultraviolet limit.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter MeasureTheory Set

/-- In the metallic regime the sharp lower-band profile is the full clean radial profile on every
finite radial interval. -/
theorem finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_lower_eq_clean
    (e v m fermiEnergy pMax : ℝ)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .lower e v m fermiEnergy pMax =
      finiteRadialCleanInterbandBastinPairIntegral .lower e v m pMax := by
  unfold finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
    finiteRadialCleanInterbandBastinPairIntegral
  apply integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with p hp
  unfold sharpRadialZeroTemperatureInterbandBastinPairLimitDensity
  rw [if_pos (bandEnergy_lower_lt_fermi v m fermiEnergy p hm hmF)]

/-- If the finite radial cutoff lies beyond the metallic Fermi radius, the sharp upper-band profile
integrates exactly to the full clean radial profile on `[0,p_F]`.  The endpoint `p_F` is handled as
a measure-zero set. -/
theorem finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_upper_eq_clean_fermiRadius
    (e v m fermiEnergy pMax : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy)
    (hpFMax : metallicFermiRadius v m fermiEnergy ≤ pMax) :
    finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .upper e v m fermiEnergy pMax =
      finiteRadialCleanInterbandBastinPairIntegral
        .upper e v m (metallicFermiRadius v m fermiEnergy) := by
  let pF := metallicFermiRadius v m fermiEnergy
  have hpFNonneg : 0 ≤ pF := by
    dsimp [pF]
    exact metallicFermiRadius_nonneg v m fermiEnergy hm hmF
  calc
    finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .upper e v m fermiEnergy pMax =
      finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .upper e v m fermiEnergy pF := by
          unfold finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
          apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
          · intro p hp
            exact ⟨hp.1, hp.2.trans hpFMax⟩
          · intro p hp
            unfold sharpRadialZeroTemperatureInterbandBastinPairLimitDensity
            rw [if_neg]
            intro hoccupied
            have hpLt : p < pF := by
              dsimp [pF]
              exact (bandEnergy_upper_lt_fermi_iff_lt_metallicFermiRadius
                v m fermiEnergy p hv hm hmF hp.1.1).1 hoccupied
            exact hp.2 ⟨hp.1.1, le_of_lt hpLt⟩
    _ = finiteRadialCleanInterbandBastinPairIntegral .upper e v m pF := by
          unfold finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
            finiteRadialCleanInterbandBastinPairIntegral
          apply integral_congr_ae
          have hne : ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) pF)), p ≠ pF := by
            refine (ae_restrict_iff' measurableSet_Icc).2 ?_
            filter_upwards [(volume : Measure ℝ).ae_ne pF] with p hpF _
            exact hpF
          have hmem : ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) pF)),
              p ∈ Set.Icc (0 : ℝ) pF :=
            MeasureTheory.ae_restrict_mem measurableSet_Icc
          filter_upwards [hne, hmem] with p hpNe hp
          unfold sharpRadialZeroTemperatureInterbandBastinPairLimitDensity
          rw [if_pos]
          dsimp [pF] at hpNe hp ⊢
          apply (bandEnergy_upper_lt_fermi_iff_lt_metallicFermiRadius
            v m fermiEnergy p hv hm hmF hp.1).2
          exact lt_of_le_of_ne hp.2 hpNe
    _ = finiteRadialCleanInterbandBastinPairIntegral
        .upper e v m (metallicFermiRadius v m fermiEnergy) := by
          rfl

/-- The sharp lower-band radial integral is the clean positive-energy shell from `m` to the radial
cutoff energy. -/
theorem finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_lower_eq_energyShell
    (e v m fermiEnergy pMax : ℝ)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) (hpMax : 0 ≤ pMax) :
    finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .lower e v m fermiEnergy pMax =
      cleanInterbandBastinPairEnergyShellIntegral
        .lower e m m (energy v m pMax 0) := by
  rw [finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_lower_eq_clean
    e v m fermiEnergy pMax hm hmF]
  exact finiteRadialCleanInterbandBastinPairIntegral_eq_energyShell
    .lower e v m pMax hm hpMax

/-- The sharp upper-band radial integral is the occupied clean positive-energy shell from `m` to
`ε_F`, provided the radial cutoff contains the Fermi radius. -/
theorem finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_upper_eq_energyShell
    (e v m fermiEnergy pMax : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy)
    (hpFMax : metallicFermiRadius v m fermiEnergy ≤ pMax) :
    finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral
        .upper e v m fermiEnergy pMax =
      cleanInterbandBastinPairEnergyShellIntegral .upper e m m fermiEnergy := by
  rw [finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_upper_eq_clean_fermiRadius
    e v m fermiEnergy pMax hv hm hmF hpFMax]
  rw [finiteRadialCleanInterbandBastinPairIntegral_eq_energyShell
    .upper e v m (metallicFermiRadius v m fermiEnergy) hm
    (metallicFermiRadius_nonneg v m fermiEnergy hm hmF)]
  rw [energy_metallicFermiRadius v m fermiEnergy hv hm hmF]

/-- Summing the exact zero-temperature lower- and upper-band radial targets gives the existing
occupied clean finite-cutoff Bastin pair weight. -/
theorem finiteRadialZeroTemperatureOccupiedInterbandBastinPairLimitIntegral_eq_occupiedCleanCutoff
    (e v m fermiEnergy pMax : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) (hpMax : 0 ≤ pMax)
    (hpFMax : metallicFermiRadius v m fermiEnergy ≤ pMax) :
    finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
        .lower e v m fermiEnergy pMax +
      finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral
        .upper e v m fermiEnergy pMax =
      occupiedCleanInterbandBastinPairCutoff
        e m fermiEnergy (energy v m pMax 0) := by
  rw [finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_lower_eq_sharp_metallic
    e v m fermiEnergy pMax hm hmF]
  rw [finiteRadialZeroTemperatureInterbandBastinPairLimitIntegral_upper_eq_sharp_metallic
    e v m fermiEnergy pMax hv hm hmF]
  rw [finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_lower_eq_energyShell
    e v m fermiEnergy pMax hm hmF hpMax]
  rw [finiteRadialSharpZeroTemperatureInterbandBastinPairLimitIntegral_upper_eq_energyShell
    e v m fermiEnergy pMax hv hm hmF hpFMax]
  rfl

/-- The physical zero-temperature finite-broadening occupied radial pair converges to the existing
clean occupied finite-cutoff pair weight.  The ultraviolet cutoff remains fixed throughout this
limit. -/
theorem tendsto_finiteRadialZeroTemperatureOccupiedInterbandBastinPairIntegral
    (e v m fermiEnergy radius pMax : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) (hpMax : 0 ≤ pMax)
    (hpFMax : metallicFermiRadius v m fermiEnergy ≤ pMax)
    (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialZeroTemperatureInterbandBastinPairIntegral
            .lower e v m fermiEnergy radius pMax broadening +
          finiteRadialZeroTemperatureInterbandBastinPairIntegral
            .upper e v m fermiEnergy radius pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (occupiedCleanInterbandBastinPairCutoff
        e m fermiEnergy (energy v m pMax 0))) := by
  have hl := tendsto_finiteRadialZeroTemperatureInterbandBastinPairIntegral
    .lower e v m fermiEnergy radius pMax hm hpMax hradiusPos hradius
  have hu := tendsto_finiteRadialZeroTemperatureInterbandBastinPairIntegral
    .upper e v m fermiEnergy radius pMax hm hpMax hradiusPos hradius
  have hsum := hl.add hu
  rw [finiteRadialZeroTemperatureOccupiedInterbandBastinPairLimitIntegral_eq_occupiedCleanCutoff
    e v m fermiEnergy pMax hv hm hmF hpMax hpFMax] at hsum
  exact hsum

end

end AnomalousHall.MassiveDirac
