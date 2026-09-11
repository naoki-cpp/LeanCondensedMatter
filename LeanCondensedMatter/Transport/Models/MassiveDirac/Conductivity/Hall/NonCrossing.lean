import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderProjection
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Non-crossing Hall benchmark for the massive Dirac model

This module owns the standard non-crossing massive-Dirac Hall conductivity benchmark of Ado et al.,
EPL 111, 37004 (2015), Eq. (3), and identifies the sequential zero-broadening then weak-disorder
Hall projection with that closed form.

Tensor completion, the antisymmetric Hall projection, and the conductivity-level weak-disorder limit
remain in `FiniteBroadeningBornLadderProjection`; this module only attaches the external benchmark
normalization `h = 2πℏ` to that result. No crossed `X/Ψ` contribution or exact disorder-average claim
is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Standard non-crossing massive-Dirac Hall conductivity of Ado et al., EPL 111, 37004 (2015),
Eq. (3), written with `h = 2πℏ`. -/
def nonCrossingHallConductivity (e hbar m probeEnergy : ℝ) : ℝ :=
  -(4 * e ^ 2 / planckFromReduced hbar) *
    (probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
      (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2)

/-- The sequential zero-broadening then weak-disorder Hall projection reproduces the Ado
non-crossing conductivity formula. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_disorder_zero_eq_nonCrossing
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : 0 < hbar)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax).hallComponent .x .y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((nonCrossingHallConductivity e hbar m probeEnergy : ℝ) : ℂ))) := by
  have h :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensorZeroBroadeningBoundary_hallComponent_disorder_zero
      e v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      (((-2 * e ^ 2 * probeEnergy * m * (probeEnergy ^ 2 + m ^ 2) /
        (Real.pi * hbar * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) =
      (((nonCrossingHallConductivity e hbar m probeEnergy : ℝ) : ℂ)) := by
    norm_cast
    unfold nonCrossingHallConductivity planckFromReduced
    field_simp [ne_of_gt hhbar, hden, Real.pi_ne_zero]
    norm_num
    ring
  rw [htarget] at h
  exact h

end

end QuantumTheory.Transport.Models.MassiveDirac
