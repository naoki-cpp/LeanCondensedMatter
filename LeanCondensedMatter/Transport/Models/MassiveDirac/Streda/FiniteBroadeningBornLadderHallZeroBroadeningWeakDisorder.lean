import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadeningTransverseWeakDisorder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening ordered transverse Středa response

The fixed-disorder `η → 0⁺` boundary is formed upstream. This module then takes the separate
one-sided `W → 0⁺` limit of the ordered source-`.y` momentum-integral response. The explicit inverse
power of `W` in the response is cancelled only after retaining the first nonvanishing transverse
ladder coefficient.

The cutoff remains fixed beyond the metallic shell. Physical conductivity normalization and the
antisymmetric Hall projection remain downstream; no ultraviolet, thermodynamic, crossed-diagram, or
simultaneous broadening/disorder limit is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- The fixed-cutoff zero-broadening ordered source-`.y` Středa momentum-integral response has a
finite one-sided weak-disorder limit. -/
theorem tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (((-16 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
          (probeEnergy ^ 2 + m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ))) := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  have hmeasureReal : momentumMeasurePrefactor hbar ≠ 0 := by
    unfold momentumMeasurePrefactor
    exact one_div_ne_zero (pow_ne_zero 2
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar))
  have hmeasure : measure ≠ 0 := by
    dsimp [measure]
    exact_mod_cast hmeasureReal
  have haction :=
    tendsto_finiteCutoffContinuumBornDysonTransverseLadderActionZeroBroadeningBoundary_div_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hscaled := haction.const_mul ((-2 : ℂ) * q ^ 2 * measure⁻¹)
  have hprobe : 0 < probeEnergy := lt_of_le_of_lt (abs_nonneg m) hmetal
  have hden : probeEnergy ^ 2 + 3 * m ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero (ne_of_gt hprobe), sq_nonneg m]
  have htarget :
      ((-2 : ℂ) * q ^ 2 * measure⁻¹) *
          (((4 * Real.pi * continuumBornAngularMeasurePrefactor hbar * probeEnergy * m *
            (probeEnergy ^ 2 + m ^ 2) /
            (v ^ 2 * (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) : ℝ) : ℂ)) =
        (((-16 * Real.pi ^ 2 * e ^ 2 * probeEnergy * m *
          (probeEnergy ^ 2 + m ^ 2) /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2 : ℝ) : ℂ)) := by
    dsimp [q, measure]
    unfold continuumBornAngularMeasurePrefactor
    push_cast
    field_simp [hvelocity, hmeasureReal, hden]
    ring
  rw [htarget] at hscaled
  apply Tendsto.congr' ?_ hscaled
  filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
  have hdisorderC : (disorderStrength : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hdisorder
  unfold finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
  dsimp [q, measure]
  push_cast
  field_simp [hdisorderC, hmeasure]

end

end QuantumTheory.Transport.Models.MassiveDirac
