import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperatureSharpShell
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Physical finite-cutoff zero-temperature massive-Dirac Bastin conductivity

The preceding sharp-shell bridge identifies the lower-plus-upper zero-temperature radial Bastin
pair with the existing occupied clean finite-cutoff pair weight.  This file restores the canonical
Bastin trace prefactor, angular factor, and physical momentum measure.

At fixed radial cutoff, the finite-broadening zero-temperature response therefore converges directly
to `bastinCleanHallConductivityCutoff`, hence to `intrinsicHallConductivityCutoff`.  The ultraviolet
limit remains a separate step.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Physical finite-radial zero-temperature Hall response before taking the positive-broadening
limit.  The two band contributions share the same Bastin trace, angular, and momentum-measure
normalization. -/
def finiteRadialZeroTemperatureBastinHallConductivity
    (e hbar v m fermiEnergy radius pMax broadening : ℝ) : ℝ :=
  bastinTraceHallPrefactor hbar *
    (2 * Real.pi * momentumMeasurePrefactor hbar) *
      (finiteRadialZeroTemperatureInterbandBastinPairIntegral
          .lower e v m fermiEnergy radius pMax broadening +
        finiteRadialZeroTemperatureInterbandBastinPairIntegral
          .upper e v m fermiEnergy radius pMax broadening)

/-- At fixed radial cutoff, the physical zero-temperature finite-broadening Bastin response
converges to the already-normalized clean finite-cutoff Bastin conductivity. -/
theorem tendsto_finiteRadialZeroTemperatureBastinHallConductivity
    (e hbar v m fermiEnergy radius pMax : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) (hpMax : 0 ≤ pMax)
    (hpFMax : metallicFermiRadius v m fermiEnergy ≤ pMax)
    (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialZeroTemperatureBastinHallConductivity
          e hbar v m fermiEnergy radius pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bastinCleanHallConductivityCutoff
        e hbar m fermiEnergy (energy v m pMax 0))) := by
  have hpair := tendsto_finiteRadialZeroTemperatureOccupiedInterbandBastinPairIntegral
    e v m fermiEnergy radius pMax hv hm hmF hpMax hpFMax hradiusPos hradius
  have htrace : Tendsto
      (fun _ : ℝ => bastinTraceHallPrefactor hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bastinTraceHallPrefactor hbar)) :=
    tendsto_const_nhds
  have hmeasure : Tendsto
      (fun _ : ℝ => 2 * Real.pi * momentumMeasurePrefactor hbar)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * Real.pi * momentumMeasurePrefactor hbar)) :=
    tendsto_const_nhds
  have hscaled := htrace.mul (hmeasure.mul hpair)
  simpa [finiteRadialZeroTemperatureBastinHallConductivity,
    bastinCleanHallConductivityCutoff, mul_assoc] using hscaled

/-- The same fixed-cutoff physical zero-temperature Bastin response converges directly to the
existing occupied-state intrinsic Hall conductivity cutoff. -/
theorem tendsto_finiteRadialZeroTemperatureBastinHallConductivity_intrinsicCutoff
    (e hbar v m fermiEnergy radius pMax : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) (hpMax : 0 ≤ pMax)
    (hpFMax : metallicFermiRadius v m fermiEnergy ≤ pMax)
    (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialZeroTemperatureBastinHallConductivity
          e hbar v m fermiEnergy radius pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (intrinsicHallConductivityCutoff
        e hbar m fermiEnergy (energy v m pMax 0))) := by
  rw [← bastinCleanHallConductivityCutoff_eq_intrinsicHallConductivityCutoff]
  exact tendsto_finiteRadialZeroTemperatureBastinHallConductivity
    e hbar v m fermiEnergy radius pMax hv hm hmF hpMax hpFMax hradiusPos hradius

end

end AnomalousHall.MassiveDirac
