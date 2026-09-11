import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadderLongitudinalZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.BornRelaxationTime
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningWeakDisorder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the scaled zero-broadening longitudinal conductivity

This module attaches the existing physical Bastin/Středa normalization to the upstream scaled
zero-broadening momentum-integral limit. The resulting finite coefficient is then identified with
the already-established microscopic Born-RTA benchmark.

The limit is sequential: `η → 0⁺` has already been taken at fixed positive disorder before the
separate `W → 0⁺` limit below. No ultraviolet, thermodynamic, SCBA/Ward, or crossed-diagram limit is
introduced.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- The disorder-scaled fixed-cutoff zero-broadening Born-Dyson longitudinal conductivity tends to
the finite Drude coefficient. -/
theorem tendsto_disorderStrength_mul_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (disorderStrength : ℂ) *
          finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((e ^ 2 * hbar * v ^ 2 * (probeEnergy ^ 2 - m ^ 2) /
          (Real.pi * (probeEnergy ^ 2 + 3 * m ^ 2)) : ℝ) : ℂ))) := by
  have hhbarNe : hbar ≠ 0 := ne_of_gt hhbar
  have hmomentum :=
    tendsto_disorderStrength_mul_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbarNe hmetal hcutoff
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      (((bastinStredaConductivityNormalization hbar : ℝ) : ℂ)) *
          (2 * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2 *
            (((momentumMeasurePrefactor hbar : ℝ) : ℂ))⁻¹ *
            (((probeEnergy ^ 2 - m ^ 2) /
              (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ)) =
        (((e ^ 2 * hbar * v ^ 2 * (probeEnergy ^ 2 - m ^ 2) /
          (Real.pi * (probeEnergy ^ 2 + 3 * m ^ 2)) : ℝ) : ℂ)) := by
    unfold bastinStredaConductivityNormalization bastinTraceConductivityPrefactor
      momentumMeasurePrefactor
    push_cast
    field_simp [hhbarNe, hden, Real.pi_ne_zero]
  simpa [
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary,
    htarget, mul_assoc, mul_left_comm, mul_comm] using
    hmomentum.const_mul (((bastinStredaConductivityNormalization hbar : ℝ) : ℂ))

/-- The scaled Born-Dyson conductivity converges directly to the microscopic Born-RTA scaled
benchmark evaluated at any positive reference disorder strength. -/
theorem tendsto_disorderStrength_mul_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary_disorder_zero_bornRelaxationTime
    (e v m probeEnergy hbar pMax referenceDisorderStrength : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hdisorder : 0 < referenceDisorderStrength)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (disorderStrength : ℂ) *
          finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((referenceDisorderStrength *
          zeroTemperatureRelaxationTimeLongitudinalConductivity
            e hbar v m probeEnergy
            (continuumBornUpperBandPositiveTransportLifetime
              v m probeEnergy referenceDisorderStrength hbar
              hvelocity hhbar hdisorder hmetal) : ℝ) : ℂ))) := by
  rw [disorderStrength_mul_zeroTemperatureRelaxationTimeLongitudinalConductivity_bornTransportLifetime_eq
    e hbar v m probeEnergy referenceDisorderStrength hvelocity hhbar hdisorder hmetal]
  exact
    tendsto_disorderStrength_mul_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff

end

end QuantumTheory.Transport.Models.MassiveDirac
