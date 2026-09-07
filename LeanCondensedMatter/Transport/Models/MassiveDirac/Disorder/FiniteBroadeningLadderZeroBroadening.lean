import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderRegularity
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningRegularity

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

/-- Zero-broadening boundary of the determinant of the normalized in-plane Born-Dyson ladder. -/
noncomputable def finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderDeterminant
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .x .x v m probeEnergy disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .y .x v m probeEnergy disorderStrength hbar pMax)

/-- Zero-broadening boundary of the solved longitudinal in-plane ladder coefficient. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedXCoefficientZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderSolvedXCoefficient
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .x .x v m probeEnergy disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .y .x v m probeEnergy disorderStrength hbar pMax)

/-- Zero-broadening boundary of the solved orientation-sensitive transverse ladder coefficient. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedYCoefficientZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderSolvedYCoefficient
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .x .x v m probeEnergy disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .y .x v m probeEnergy disorderStrength hbar pMax)

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
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
            .x .x v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
            .y .x v m probeEnergy broadening disorderStrength hbar pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hX :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .x .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hY :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .y .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hOne :
      Tendsto (fun _ : ℝ => (1 : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    tendsto_const_nhds
  have hOneMinusX := hOne.sub hX
  simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary,
    inPlaneLadderDeterminant, pow_two] using
    (hOneMinusX.mul hOneMinusX).add (hY.mul hY)

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

/-- The solved longitudinal ladder coefficient converges at fixed disorder whenever the boundary
ladder determinant is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderSolvedXCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
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
        finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderSolvedXCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hX :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .x .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hdetLimit :=
    tendsto_finiteCutoffContinuumBornDysonLadderDeterminant_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hOne :
      Tendsto (fun _ : ℝ => (1 : ℂ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    tendsto_const_nhds
  have hnum := hOne.sub hX
  simpa [finiteCutoffContinuumBornDysonLadderSolvedXCoefficient,
    finiteCutoffContinuumBornDysonLadderSolvedXCoefficientZeroBroadeningBoundary,
    finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary,
    inPlaneLadderSolvedXCoefficient, div_eq_mul_inv] using
    hnum.mul (hdetLimit.inv₀ hdet)

/-- The solved orientation-sensitive transverse ladder coefficient converges at fixed disorder
whenever the boundary ladder determinant is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderSolvedYCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
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
        finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderSolvedYCoefficientZeroBroadeningBoundary
          v m probeEnergy disorderStrength hbar pMax)) := by
  have hY :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .y .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hdetLimit :=
    tendsto_finiteCutoffContinuumBornDysonLadderDeterminant_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  simpa [finiteCutoffContinuumBornDysonLadderSolvedYCoefficient,
    finiteCutoffContinuumBornDysonLadderSolvedYCoefficientZeroBroadeningBoundary,
    finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary,
    inPlaneLadderSolvedYCoefficient, div_eq_mul_inv] using
    hY.mul (hdetLimit.inv₀ hdet)

end

end QuantumTheory.Transport.Models.MassiveDirac
