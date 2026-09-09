import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningIntegral

set_option linter.style.header false

/-!
# Zero-broadening boundary of the finite-cutoff Born-Dyson ladder

At fixed positive disorder and finite cutoff, the integrated current-rung boundary determines the
zero-broadening boundary of the canonical in-plane ladder. The only additional analytic condition is
nonvanishing of the boundary determinant of `I - L`; no disorder-strength or ultraviolet limit is
taken here.

The repository orientation remains `[[X,-Y],[Y,X]]`, corresponding to `Gᴿ Γ Gᴬ`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter

/-- Canonical zero-broadening boundary of the source-`σₓ` current rung. -/
noncomputable def finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : InPlaneCoefficientVector :=
  fun output =>
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      output .x v m probeEnergy disorderStrength hbar pMax

/-- Zero-broadening boundary of the determinant of the normalized in-plane Born-Dyson ladder. -/
noncomputable def finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderDeterminant
    (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax)

/-- Canonical zero-broadening boundary of the solved in-plane ladder for a bare `σₓ` source. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : InPlaneCoefficientVector :=
  inPlaneLadderSolvedVector
    (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax)

private theorem tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonCurrentRungVector
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  rw [tendsto_pi_nhds]
  intro output
  cases output
  · exact
      tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
        .x .x v m probeEnergy disorderStrength hbar pMax
        hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  · exact
      tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
        .y .x v m probeEnergy disorderStrength hbar pMax
        hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm

/-- The finite-`η` ladder determinant converges to its fixed-disorder zero-broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderDeterminant_broadening_zero_of_boundary_realRenormalization_lt_one
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1) :
    Tendsto
      (fun broadening : ℝ =>
        inPlaneLadderDeterminant
          (finiteCutoffContinuumBornDysonCurrentRungVector
            v m probeEnergy broadening disorderStrength hbar pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary] using
    tendsto_inPlaneLadderDeterminant hrung

/-- A nonzero boundary determinant implies finite-`η` ladder regularity for all sufficiently small
positive broadenings. -/
theorem eventually_finiteCutoffContinuumBornDysonLadderRegular_broadening_zero_of_boundary_realRenormalization_lt_one
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1)
    (hdet :
      finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax ≠ 0) :
    ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      finiteCutoffContinuumBornDysonLadderRegular
        v m probeEnergy broadening disorderStrength hbar pMax := by
  have hdetLimit :=
    tendsto_finiteCutoffContinuumBornDysonLadderDeterminant_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  filter_upwards [hdetLimit.eventually_ne hdet] with broadening hbroadening
  exact hbroadening

/-- The solved in-plane ladder vector converges at fixed disorder whenever the boundary determinant
is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
    (v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        v m probeEnergy disorderStrength hbar pMax < 1)
    (hdet :
      finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
        v m probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonLadderSolvedVector
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hdet' :
      inPlaneLadderDeterminant
        (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax) ≠ 0 := by
    simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary] using hdet
  simpa [finiteCutoffContinuumBornDysonLadderSolvedVector,
    finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary] using
    (tendsto_inPlaneLadderSolvedVector hrung hdet')

end

end QuantumTheory.Transport.Models.MassiveDirac
