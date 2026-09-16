import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalSameSide
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadeningWeakDisorder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Weak-disorder limit of the zero-broadening longitudinal Středa momentum integral

The zero-broadening boundary is formed first at fixed disorder. This module then takes the separate
one-sided `W → 0⁺` limit after multiplying the longitudinal momentum integral by `W`. The singular
retarded-advanced term is controlled by the canonical ladder-action limit, while the same-side
endpoint contribution consumes its own model-local weak-disorder limit.

The cutoff remains fixed beyond the metallic shell. Physical conductivity normalization remains
owned downstream by `MassiveDirac.Conductivity`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- After the fixed-cutoff zero-broadening boundary is formed, multiplying the longitudinal Středa
momentum integral by the disorder strength gives a finite weak-disorder limit. -/
theorem tendsto_disorderStrength_mul_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary_disorder_zero
    (e v m probeEnergy hbar pMax : ℝ)
    (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2) :
    Tendsto
      (fun disorderStrength : ℝ =>
        (disorderStrength : ℂ) *
          finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
            e v m probeEnergy disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (2 * ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) ^ 2 *
          (((momentumMeasurePrefactor hbar : ℝ) : ℂ))⁻¹ *
          (((probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) : ℝ) : ℂ))) := by
  let q : ℂ := (((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))
  let measure : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  have hmeasureReal : momentumMeasurePrefactor hbar ≠ 0 := by
    unfold momentumMeasurePrefactor
    exact one_div_ne_zero (pow_ne_zero 2
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar))
  have hmeasure : measure ≠ 0 := by
    dsimp [measure]
    exact_mod_cast hmeasureReal
  have hRR := tendsto_disorderStrength_mul_zeroBroadeningSameSideRadialEndpoint_disorder_zero
    .retarded v m probeEnergy hbar pMax hmetal hcutoff
  have hAA := tendsto_disorderStrength_mul_zeroBroadeningSameSideRadialEndpoint_disorder_zero
    .advanced v m probeEnergy hbar pMax hmetal hcutoff
  have haction :=
    tendsto_finiteCutoffContinuumBornDysonLongitudinalLadderActionZeroBroadeningBoundary_disorder_zero
      v m probeEnergy hbar pMax hvelocity hhbar hmetal hcutoff
  have hRA := haction.const_mul (2 * q ^ 2 * measure⁻¹)
  have hSame :=
    (hRR.add hAA).const_mul ((((2 * Real.pi : ℝ) : ℂ)) * q ^ 2)
  have hTotal := hRA.sub hSame
  simp only [add_zero, mul_zero, sub_zero] at hTotal
  apply Tendsto.congr' ?_ (by simpa [q, measure] using hTotal)
  filter_upwards [self_mem_nhdsWithin] with disorderStrength hdisorder
  have hdisorderC : (disorderStrength : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hdisorder
  have hboundary :
      finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax =
        2 * q ^ 2 *
            (((disorderStrength * momentumMeasurePrefactor hbar : ℝ) : ℂ))⁻¹ *
            inPlaneLadderAction
              (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
                v m probeEnergy disorderStrength hbar pMax)
              (finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
                v m probeEnergy disorderStrength hbar pMax) 0 -
          (((2 * Real.pi : ℝ) : ℂ)) * q ^ 2 *
            (zeroBroadeningSameSideRadialEndpoint
                .retarded v m probeEnergy disorderStrength hbar pMax +
              zeroBroadeningSameSideRadialEndpoint
                .advanced v m probeEnergy disorderStrength hbar pMax) := by
    rfl
  rw [hboundary]
  simp only [inPlaneLadderAction_apply_x,
    finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary]
  push_cast
  dsimp [q, measure] at hmeasure ⊢
  push_cast
  field_simp [hdisorderC, hmeasure]

end

end QuantumTheory.Transport.Models.MassiveDirac
