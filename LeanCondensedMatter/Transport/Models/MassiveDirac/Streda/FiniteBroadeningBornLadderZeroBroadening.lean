import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder

set_option linter.style.header false

/-!
# Zero-broadening boundary of the Born-Dyson dressed source current

At fixed positive disorder and finite cutoff, this module propagates the solved in-plane ladder
boundary into the source-indexed retarded-advanced dressed current consumed by the Středa response.
The repository rotation convention remains `[[α,-β],[β,α]]`.

The finite-broadening current is the total algebraic value built from the two solved ladder
coefficients. The nonzero limiting ladder determinant remains explicit in the convergence theorem
because it controls the solved-coefficient limit and its fixed-point interpretation. No Středa
momentum integral, conductivity normalization, weak-disorder limit, or ultraviolet removal is
introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Fixed-cutoff zero-broadening boundary of the source-indexed RA dressed current operator. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary
    (source : Direction2)
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  let alpha := finiteCutoffContinuumBornDysonLadderSolvedCoefficientZeroBroadeningBoundary
    .x v m probeEnergy disorderStrength hbar pMax
  let beta := finiteCutoffContinuumBornDysonLadderSolvedCoefficientZeroBroadeningBoundary
    .y v m probeEnergy disorderStrength hbar pMax
  inPlaneCurrentOperator e v
    (inPlaneRotationCoefficient alpha beta .x source)
    (inPlaneRotationCoefficient alpha beta .y source)

/-- At fixed positive disorder, every source-indexed RA dressed current approaches the current built
from the solved zero-broadening ladder coefficients. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_broadening_zero_of_boundary_realRenormalization_lt_one
    (source : Direction2)
    (e v m probeEnergy disorderStrength hbar pMax : ℝ)
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
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
          source e v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary
          source e v m probeEnergy disorderStrength hbar pMax)) := by
  have hAlpha :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .x v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm hdet
  have hBeta :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedCoefficient_broadening_zero_of_boundary_realRenormalization_lt_one
      .y v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm hdet
  have hX := tendsto_inPlaneRotationCoefficient hAlpha hBeta .x source
  have hY := tendsto_inPlaneRotationCoefficient hAlpha hBeta .y source
  simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary,
    inPlaneCurrentOperator] using
    (hX.smul_const (currentOperator .x e v)).add
      (hY.smul_const (currentOperator .y e v))

end

end QuantumTheory.Transport.Models.MassiveDirac
