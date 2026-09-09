import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder

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

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter
open QuantumTheory.Transport

/-- Fixed-cutoff zero-broadening boundary of the source-indexed RA dressed current operator. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary
    (source : Direction2)
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  let solved := finiteCutoffContinuumBornDysonLadderSolvedVectorZeroBroadeningBoundary
    v m probeEnergy disorderStrength hbar pMax
  let dressed := Matrix.transpose (inPlaneRotationMatrix solved) source
  inPlaneCurrentOperator e v (dressed .x) (dressed .y)

/-- At fixed positive disorder, every source-indexed RA dressed current approaches the current built
from the solved zero-broadening ladder vector. -/
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
  have hSolved :=
    tendsto_finiteCutoffContinuumBornDysonLadderSolvedVector_broadening_zero_of_boundary_realRenormalization_lt_one
      v m probeEnergy disorderStrength hbar pMax
      hpMax hvelocity hhbar hdisorder hmetal hcutoff hrenorm hdet
  have hAlpha := tendsto_pi_nhds.mp hSolved .x
  have hBeta := tendsto_pi_nhds.mp hSolved .y
  cases source
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary,
      inPlaneCurrentOperator, Matrix.transpose, inPlaneRotationMatrix] using
      (hAlpha.smul_const (currentOperator .x e v)).add
        (hBeta.smul_const (currentOperator .y e v))
  · simpa [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary,
      inPlaneCurrentOperator, Matrix.transpose, inPlaneRotationMatrix] using
      (hBeta.neg.smul_const (currentOperator .x e v)).add
        (hAlpha.smul_const (currentOperator .y e v))

end

end QuantumTheory.Transport.Models.MassiveDirac
