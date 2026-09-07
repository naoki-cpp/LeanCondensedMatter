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

/-- Zero-broadening boundary of the determinant of the normalized in-plane Born-Dyson ladder. -/
noncomputable def finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  inPlaneLadderDeterminant
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .x .x v m probeEnergy disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .y .x v m probeEnergy disorderStrength hbar pMax)

/-- Zero-broadening boundary of one output component of the solved in-plane ladder for a bare
`σₓ` source. -/
noncomputable def finiteCutoffContinuumBornDysonLadderSolvedCoefficientZeroBroadeningBoundary
    (output : Direction2) (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  let x :=
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .x .x v m probeEnergy disorderStrength hbar pMax
  let y :=
    finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
      .y .x v m probeEnergy disorderStrength hbar pMax
  inPlaneLadderSolvedCoefficient output x y

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

/-- Every output component of the solved ladder converges at fixed disorder whenever the boundary
ladder determinant is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderSolvedCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
    (output : Direction2) (v m probeEnergy disorderStrength hbar pMax : ℝ)
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
        finiteCutoffContinuumBornDysonLadderSolvedCoefficient
          output v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderSolvedCoefficientZeroBroadeningBoundary
          output v m probeEnergy disorderStrength hbar pMax)) := by
  have hX :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .x .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hY :=
    tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .y .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm
  have hdet' :
      inPlaneLadderDeterminant
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          .x .x v m probeEnergy disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficientZeroBroadeningBoundary
          .y .x v m probeEnergy disorderStrength hbar pMax) ≠ 0 := by
    simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary] using hdet
  simpa [finiteCutoffContinuumBornDysonLadderSolvedCoefficient,
    finiteCutoffContinuumBornDysonLadderSolvedCoefficientZeroBroadeningBoundary] using
    (tendsto_inPlaneLadderSolvedCoefficient hX hY hdet' output)

end

end QuantumTheory.Transport.Models.MassiveDirac
