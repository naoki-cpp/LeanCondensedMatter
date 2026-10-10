import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadeningIntegral
import LeanCondensedMatter.Models.MassiveDirac.TransportDomain

set_option linter.style.header false

/-!
# Zero-broadening boundary of the finite-cutoff Born-Dyson ladder

At fixed positive disorder and finite cutoff, the integrated current-rung boundary determines the
zero-broadening boundary of the canonical in-plane ladder. The only additional analytic condition is
nonvanishing of the boundary determinant of `I - L`; no disorder-strength or ultraviolet limit is
taken here.

The repository orientation remains `[[X,-Y],[Y,X]]`, corresponding to `Gᴿ Γ Gᴬ`.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open Filter

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

/-- The finite-`η` ladder determinant converges to its fixed-disorder zero-broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderDeterminant_broadening_zero_of_boundary_realRenormalization_lt_one
    (regime : FixedCutoffMetallicBornRegime)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax < 1) :
    Tendsto
      (fun broadening : ℝ =>
        inPlaneLadderDeterminant
          (finiteCutoffContinuumBornDysonCurrentRungVector
            regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar regime.pMax))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
          regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax)) := by
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm
  simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary] using
    tendsto_inPlaneLadderDeterminant hrung

/-- A nonzero boundary determinant implies finite-`η` ladder regularity for all sufficiently small
positive broadenings. -/
theorem eventually_finiteCutoffContinuumBornDysonLadderRegular_broadening_zero_of_boundary_realRenormalization_lt_one
    (regime : FixedCutoffMetallicBornRegime)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax < 1)
    (hdet :
      finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
        regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax ≠ 0) :
    ∀ᶠ broadening : ℝ in nhdsWithin 0 (Set.Ioi 0),
      finiteCutoffContinuumBornDysonLadderRegular
        regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar regime.pMax := by
  have hdetLimit :=
    tendsto_finiteCutoffContinuumBornDysonLadderDeterminant_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm
  filter_upwards [hdetLimit.eventually_ne hdet] with broadening hbroadening
  exact hbroadening

/-- The solved in-plane ladder vector converges at fixed disorder whenever the boundary determinant
is nonzero. -/
theorem tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
    (regime : FixedCutoffMetallicBornRegime)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax < 1)
    (hdet :
      finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
        regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonLadderSolvedVector
          regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar regime.pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
          regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax)) := by
  have hrung :=
    tendsto_finiteCutoffContinuumBornDysonCurrentRungVector_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm
  have hdet' :
      inPlaneLadderDeterminant
        (finiteCutoffContinuumBornDysonCurrentRungVectorZeroBroadeningBoundary
          regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax) ≠ 0 := by
    simpa [finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary] using hdet
  simpa [finiteCutoffContinuumBornDysonLadderSolvedVector,
    finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary] using
    (tendsto_inPlaneLadderSolvedVector hrung hdet')

end

end QuantumTheory.Models.MassiveDirac
