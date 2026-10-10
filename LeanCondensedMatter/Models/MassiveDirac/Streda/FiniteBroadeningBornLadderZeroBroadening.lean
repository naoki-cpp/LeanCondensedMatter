import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder

set_option linter.style.header false

/-!
# Zero-broadening boundary of the Born-Dyson dressed source current

At fixed positive disorder and finite cutoff, this module propagates the solved in-plane ladder
boundary into the source-indexed retarded-advanced dressed current consumed by the Středa response.
The repository rotation convention remains `[[α,-β],[β,α]]`.

The finite-broadening current is the total algebraic value built from the solved ladder vector. The
nonzero limiting ladder determinant remains explicit in the convergence theorem because it controls
the solved-vector limit and its fixed-point interpretation. No Středa momentum integral,
conductivity normalization, weak-disorder limit, or ultraviolet removal is introduced here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Fixed-cutoff zero-broadening boundary of the source-indexed RA dressed current operator. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary
    (source : Fin 2)
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
    v m probeEnergy disorderStrength hbar pMax
  let dressed := Matrix.transpose (inPlaneRotationMatrix solved) source
  inPlaneCurrentOperator e v dressed

/-- At fixed positive disorder, every source-indexed RA dressed current approaches the current built
from the solved zero-broadening ladder vector. -/
theorem tendsto_finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_broadening_zero_of_boundary_realRenormalization_lt_one
    (source : Fin 2)
    (e : ℝ) (regime : FixedCutoffMetallicBornRegime)
    (hrenorm :
      finiteCutoffContinuumBornBoundaryRealRenormalization
        regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax < 1)
    (hdet :
      finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
        regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
          source e regime.v regime.m regime.probeEnergy broadening regime.disorderStrength regime.hbar regime.pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary
          source e regime.v regime.m regime.probeEnergy regime.disorderStrength regime.hbar regime.pMax)) := by
  have hSolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
      regime hrenorm hdet
  have hAlpha := tendsto_pi_nhds.mp hSolved 0
  have hBeta := tendsto_pi_nhds.mp hSolved 1
  fin_cases source
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary,
      inPlaneCurrentOperator, Matrix.transpose, inPlaneRotationMatrix] using
      (hAlpha.smul_const (currentOperator 0 e regime.v)).add
        (hBeta.smul_const (currentOperator 1 e regime.v))
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary,
      inPlaneCurrentOperator, Matrix.transpose, inPlaneRotationMatrix] using
      (hBeta.neg.smul_const (currentOperator 0 e regime.v)).add
        (hAlpha.smul_const (currentOperator 1 e regime.v))

end

end QuantumTheory.Models.MassiveDirac
