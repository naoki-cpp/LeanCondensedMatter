import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfaceConductivity
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinZeroTemperatureUV
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Clean Středa sea remainder for the massive Dirac cone

The zero-temperature Bastin response and the Středa surface response now live at the same physical
normalization. This file defines the residual response at that common level and identifies its fixed
finite-cutoff clean limit.

For the metallic benchmark the residual term is exactly the single-cone cutoff correction

```text
σxy^sea(Λ) = +(e² / 2h) (m / Λ),
```

and therefore vanishes when the ultraviolet cutoff is removed.

This is a response-level residual statement. It does not identify the zero-temperature radial
remainder directly with the smooth finite-broadening momentum-fiber object
`massiveDiracRegularizedStredaFermiSea`; that bridge remains a separate analytic statement.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter

/-- Clean finite-cutoff Středa sea remainder at the physical conductivity level. -/
def cleanStredaSeaRemainderHallConductivityCutoff
    (e hbar m fermiEnergy energyCutoff : ℝ) : ℝ :=
  intrinsicHallConductivityCutoff e hbar m fermiEnergy energyCutoff -
    intrinsicHallConductivity e hbar m fermiEnergy

/-- Before taking the positive-broadening limit, define the radial sea remainder by exact subtraction
of the normalized Středa surface response from the normalized zero-temperature Bastin response. -/
def finiteRadialStredaSeaRemainderHallConductivity
    (e hbar v m fermiEnergy radius pMax broadening : ℝ) : ℝ :=
  finiteRadialZeroTemperatureBastinHallConductivity
      e hbar v m fermiEnergy radius pMax broadening -
    finiteRadialStredaSurfaceHallConductivity
      e hbar v m fermiEnergy pMax broadening

/-- The finite-broadening physical response decomposes tautologically into the named surface term
plus the residual sea term. -/
theorem finiteRadialZeroTemperatureBastinHallConductivity_eq_surface_add_seaRemainder
    (e hbar v m fermiEnergy radius pMax broadening : ℝ) :
    finiteRadialZeroTemperatureBastinHallConductivity
        e hbar v m fermiEnergy radius pMax broadening =
      finiteRadialStredaSurfaceHallConductivity
          e hbar v m fermiEnergy pMax broadening +
        finiteRadialStredaSeaRemainderHallConductivity
          e hbar v m fermiEnergy radius pMax broadening := by
  unfold finiteRadialStredaSeaRemainderHallConductivity
  ring

/-- The clean finite-cutoff residual is the negative Hall prefactor times the omitted valence-band
Berry tail. -/
theorem cleanStredaSeaRemainderHallConductivityCutoff_eq_prefactor_correction
    (e hbar m fermiEnergy energyCutoff : ℝ)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) (hFCutoff : fermiEnergy ≤ energyCutoff) :
    cleanStredaSeaRemainderHallConductivityCutoff
        e hbar m fermiEnergy energyCutoff =
      -(intrinsicHallPrefactorFromMomentumMeasure e hbar) *
        (m / (2 * energyCutoff)) := by
  unfold cleanStredaSeaRemainderHallConductivityCutoff
    intrinsicHallConductivityCutoff intrinsicHallConductivity
  rw [metallicBerryWeightCutoff_eq m fermiEnergy energyCutoff hm hmF hFCutoff]
  unfold metallicBerryWeightUV
  ring

/-- In physical units the clean finite-cutoff sea remainder is
`+(e² / 2h) (m / Λ)`. -/
theorem cleanStredaSeaRemainderHallConductivityCutoff_eq_massiveDirac
    (e hbar m fermiEnergy energyCutoff : ℝ)
    (hhbar : 0 < hbar) (hm : 0 < m)
    (hmF : m ≤ fermiEnergy) (hFCutoff : fermiEnergy ≤ energyCutoff) :
    cleanStredaSeaRemainderHallConductivityCutoff
        e hbar m fermiEnergy energyCutoff =
      (e ^ 2 / (2 * planckFromReduced hbar)) * (m / energyCutoff) := by
  rw [cleanStredaSeaRemainderHallConductivityCutoff_eq_prefactor_correction
      e hbar m fermiEnergy energyCutoff hm hmF hFCutoff,
    intrinsicHallPrefactorFromMomentumMeasure_eq e hbar hhbar.ne']
  have hfermi : 0 < fermiEnergy := lt_of_lt_of_le hm hmF
  have hcutoff : 0 < energyCutoff := lt_of_lt_of_le hfermi hFCutoff
  unfold planckFromReduced
  field_simp [hhbar.ne', hcutoff.ne', Real.pi_ne_zero]

/-- At fixed radial cutoff, the residual finite-broadening response converges to the clean finite
cutoff sea remainder. -/
theorem tendsto_finiteRadialStredaSeaRemainderHallConductivity
    (e hbar v m fermiEnergy radius pMax : ℝ) (hv : v ≠ 0)
    (hhbar : 0 < hbar) (hm : 0 < m) (hmF : m < fermiEnergy)
    (hpMax : 0 ≤ pMax)
    (hpFMax : metallicFermiRadius v m fermiEnergy ≤ pMax)
    (hFMax : fermiEnergy < energy v m pMax 0)
    (hradiusPos : 0 < radius) (hradius : radius < 2 * m) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialStredaSeaRemainderHallConductivity
          e hbar v m fermiEnergy radius pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (cleanStredaSeaRemainderHallConductivityCutoff
        e hbar m fermiEnergy (energy v m pMax 0))) := by
  have htotal :=
    tendsto_finiteRadialZeroTemperatureBastinHallConductivity_intrinsicCutoff
      e hbar v m fermiEnergy radius pMax hv hm hmF.le hpMax hpFMax hradiusPos hradius
  have hsurface :=
    tendsto_finiteRadialStredaSurfaceHallConductivity_intrinsic
      e hbar v m fermiEnergy pMax hhbar hm hpMax hmF hFMax
  simpa [finiteRadialStredaSeaRemainderHallConductivity,
    cleanStredaSeaRemainderHallConductivityCutoff] using htotal.sub hsurface

/-- Removing the positive-energy ultraviolet cutoff eliminates the clean Středa sea remainder. -/
theorem tendsto_cleanStredaSeaRemainderHallConductivityCutoff_atTop
    (e hbar m fermiEnergy : ℝ) (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    Tendsto
      (cleanStredaSeaRemainderHallConductivityCutoff e hbar m fermiEnergy)
      atTop (nhds 0) := by
  have htotal := tendsto_intrinsicHallConductivityCutoff_atTop
    e hbar m fermiEnergy hm hmF
  have hsurface : Tendsto
      (fun _ : ℝ => intrinsicHallConductivity e hbar m fermiEnergy)
      atTop (nhds (intrinsicHallConductivity e hbar m fermiEnergy)) :=
    tendsto_const_nhds
  change Tendsto
    (fun energyCutoff : ℝ =>
      intrinsicHallConductivityCutoff e hbar m fermiEnergy energyCutoff -
        intrinsicHallConductivity e hbar m fermiEnergy)
    atTop (nhds 0)
  simpa using htotal.sub hsurface

/-- Equivalently, for nonzero Dirac velocity the residual vanishes as the radial cutoff tends to
`+∞`. -/
theorem tendsto_cleanStredaSeaRemainderHallConductivityCutoff_radial_atTop
    (e hbar v m fermiEnergy : ℝ) (hv : v ≠ 0)
    (hm : 0 < m) (hmF : m ≤ fermiEnergy) :
    Tendsto
      (fun pMax : ℝ => cleanStredaSeaRemainderHallConductivityCutoff
        e hbar m fermiEnergy (energy v m pMax 0))
      atTop (nhds 0) := by
  exact (tendsto_cleanStredaSeaRemainderHallConductivityCutoff_atTop
    e hbar m fermiEnergy hm hmF).comp (tendsto_energy_radial_atTop v m hv)

end

end AnomalousHall.MassiveDirac
