import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSurfaceEnergyLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinCleanConductivity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Physical clean Středa surface conductivity for the massive Dirac cone

This file reconnects the exact radial Středa surface primitive to the closed energy kernel and then
restores the same Bastin trace, angular, and physical-momentum normalization used by the already
closed clean Hall benchmark.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Finite radial integral of the real part of the named Středa surface primitive. -/
def finiteRadialStredaSurfacePrimitiveIntegral
    (e v m fermiEnergy pMax broadening : ℝ) : ℝ :=
  ∫ p in (0 : ℝ)..pMax,
    p * (regularizedStredaSurfacePrimitiveTrace
      (hamiltonianOperator v m p 0)
      (currentXOperator e v) (currentYOperator e v)
      fermiEnergy broadening).re

/-- At positive mass and broadening, the named radial surface primitive is exactly the closed real
interband kernel derived upstream. -/
theorem finiteRadialStredaSurfacePrimitiveIntegral_eq_kernelIntegral
    (e v m fermiEnergy pMax broadening : ℝ)
    (hm : 0 < m) (hbroadening : 0 < broadening) :
    finiteRadialStredaSurfacePrimitiveIntegral e v m fermiEnergy pMax broadening =
      ∫ p in (0 : ℝ)..pMax,
        p * radialInterbandStredaSurfaceKernel
          e v m fermiEnergy (energy v m p 0) broadening := by
  unfold finiteRadialStredaSurfacePrimitiveIntegral
  apply intervalIntegral.integral_congr
  intro p _
  have hE : energy v m p 0 ≠ 0 :=
    ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)
  rw [regularizedStredaSurfacePrimitiveTrace_radial_eq_interband
      e v m p fermiEnergy broadening hE hbroadening,
    interbandStredaSurfaceTraceContribution_radial_eq_kernel
      e v m p fermiEnergy broadening hE hbroadening]
  simp

/-- The finite radial integral of the actual Středa surface primitive equals the positive-energy
surface integral. -/
theorem finiteRadialStredaSurfacePrimitiveIntegral_eq_energyIntegral
    (e v m fermiEnergy pMax broadening : ℝ)
    (hm : 0 < m) (hpMax : 0 ≤ pMax) (hbroadening : 0 < broadening) :
    finiteRadialStredaSurfacePrimitiveIntegral e v m fermiEnergy pMax broadening =
      finiteEnergyStredaSurfaceIntegral
        e m fermiEnergy (energy v m pMax 0) broadening := by
  rw [finiteRadialStredaSurfacePrimitiveIntegral_eq_kernelIntegral
    e v m fermiEnergy pMax broadening hm hbroadening]
  exact finiteRadialInterbandStredaSurfaceIntegral_eq_energyIntegral
    e v m fermiEnergy pMax broadening hm hpMax hbroadening.ne'

/-- Physical finite-radial Středa surface Hall conductivity, with the same normalization convention
as `bastinCleanHallConductivityCutoff`. -/
def finiteRadialStredaSurfaceHallConductivity
    (e hbar v m fermiEnergy pMax broadening : ℝ) : ℝ :=
  bastinTraceHallPrefactor hbar *
    (2 * Real.pi * momentumMeasurePrefactor hbar) *
      finiteRadialStredaSurfacePrimitiveIntegral
        e v m fermiEnergy pMax broadening

/-- At positive broadening the physical surface response can be evaluated entirely in the positive
energy coordinate. -/
theorem finiteRadialStredaSurfaceHallConductivity_eq_energyIntegral
    (e hbar v m fermiEnergy pMax broadening : ℝ)
    (hm : 0 < m) (hpMax : 0 ≤ pMax) (hbroadening : 0 < broadening) :
    finiteRadialStredaSurfaceHallConductivity
        e hbar v m fermiEnergy pMax broadening =
      bastinTraceHallPrefactor hbar *
        (2 * Real.pi * momentumMeasurePrefactor hbar) *
          finiteEnergyStredaSurfaceIntegral
            e m fermiEnergy (energy v m pMax 0) broadening := by
  unfold finiteRadialStredaSurfaceHallConductivity
  rw [finiteRadialStredaSurfacePrimitiveIntegral_eq_energyIntegral
    e v m fermiEnergy pMax broadening hm hpMax hbroadening]

/-- If the fixed radial cutoff contains the metallic Fermi shell, the positive-broadening Středa
surface conductivity converges to the continuum intrinsic massive-Dirac Hall response. -/
theorem tendsto_finiteRadialStredaSurfaceHallConductivity_intrinsic
    (e hbar v m fermiEnergy pMax : ℝ)
    (hhbar : 0 < hbar) (hm : 0 < m) (hpMax : 0 ≤ pMax)
    (hmF : m < fermiEnergy) (hFMax : fermiEnergy < energy v m pMax 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteRadialStredaSurfaceHallConductivity
          e hbar v m fermiEnergy pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (intrinsicHallConductivity e hbar m fermiEnergy)) := by
  have hraw := tendsto_finiteEnergyStredaSurfaceIntegral
    e m fermiEnergy (energy v m pMax 0) hm hmF hFMax
  have hconst : Tendsto
      (fun _ : ℝ =>
        bastinTraceHallPrefactor hbar *
          (2 * Real.pi * momentumMeasurePrefactor hbar))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bastinTraceHallPrefactor hbar *
          (2 * Real.pi * momentumMeasurePrefactor hbar))) :=
    tendsto_const_nhds
  have hscaled := hconst.mul hraw
  have hresponse : Tendsto
      (fun broadening : ℝ =>
        finiteRadialStredaSurfaceHallConductivity
          e hbar v m fermiEnergy pMax broadening)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bastinTraceHallPrefactor hbar *
          (2 * Real.pi * momentumMeasurePrefactor hbar) *
            (-(e ^ 2 * m / fermiEnergy) * Real.pi))) := by
    apply Tendsto.congr' ?_ hscaled
    filter_upwards [self_mem_nhdsWithin] with broadening hbroadening
    rw [finiteRadialStredaSurfaceHallConductivity_eq_energyIntegral
      e hbar v m fermiEnergy pMax broadening hm hpMax hbroadening]
  have hfermi : 0 < fermiEnergy := lt_trans hm hmF
  have hnorm :
      bastinTraceHallPrefactor hbar *
          (2 * Real.pi * momentumMeasurePrefactor hbar) *
            (-(e ^ 2 * m / fermiEnergy) * Real.pi) =
        intrinsicHallConductivity e hbar m fermiEnergy := by
    rw [intrinsicHallConductivity_eq_massiveDirac e hbar m fermiEnergy hhbar hfermi]
    unfold bastinTraceHallPrefactor momentumMeasurePrefactor planckFromReduced
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hhbar.ne', hfermi.ne', hpi]
    ring
  rw [hnorm] at hresponse
  exact hresponse

end

end AnomalousHall.MassiveDirac
