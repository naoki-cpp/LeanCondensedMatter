import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson dressed current insertion

This module is the response seam for the finite-cutoff finite-broadening Born-Dyson current
vertex. The current-rung implementation owns angular reduction, radial normalization, and the
algebraic ladder solution; this module exposes the source-indexed dressed in-plane coefficient and
its current-operator realization to response consumers.

The coefficient and operator values are total algebraic constructions. The separate ladder
regularity predicate is still required when a consumer interprets them as the physical fixed-point
vertex. The longitudinal factor is exposed separately for reduced crossed responses; it is not the
full two-component dressed vertex.

The fixed-disorder zero-broadening boundary of the same insertion is owned here as well. No Streda
trace, Gaussian-crossed Fourier kernel, same-side remainder, or conductivity normalization is owned
here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport Filter

/-! ## Source-indexed response insertion -/

/-- Source-indexed finite-cutoff finite-`η` Born-Dyson dressed in-plane coefficient vector. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : InPlaneCoefficientVector :=
  Matrix.transpose (inPlaneRotationMatrix
    (finiteCutoffContinuumBornDysonLadderSolvedVector
      v m probeEnergy broadening disorderStrength hbar pMax)) source

/-- The source-`x` dressed coefficients are the canonical solved ladder vector. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector_x
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
        0 v m probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonLadderSolvedVector
        v m probeEnergy broadening disorderStrength hbar pMax := by
  funext direction
  fin_cases direction <;>
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector,
      Matrix.transpose, inPlaneRotationMatrix]

/-- The source-`y` coefficients follow the same repository rotation convention as source `x`. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector_y
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
        1 v m probeEnergy broadening disorderStrength hbar pMax =
      let solved := finiteCutoffContinuumBornDysonLadderSolvedVector
        v m probeEnergy broadening disorderStrength hbar pMax;
      inPlaneCoefficientVector (-(solved 1)) (solved 0) := by
  funext direction
  fin_cases direction <;>
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector,
      Matrix.transpose, inPlaneRotationMatrix, inPlaneCoefficientVector]

/-- Source-indexed finite-cutoff finite-`η` Born-Dyson dressed current insertion. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    (source : Fin 2)
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneCurrentOperator e v
    (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
      source v m probeEnergy broadening disorderStrength hbar pMax)

/-! ## Algebraic and physical-fixed-point bridge -/

/-- Under ladder regularity, the source-`x` insertion is the canonical resummed ladder vertex. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_x_eq_resummed
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hregular : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
        0 e v m probeEnergy broadening disorderStrength hbar pMax =
      inPlaneCurrentOperator e v
        (resummedLadderVertex
          (inPlaneLadderCLM
            (finiteCutoffContinuumBornDysonCurrentRungVector
              v m probeEnergy broadening disorderStrength hbar pMax))
          (inPlaneLadderShift_isUnit
            (finiteCutoffContinuumBornDysonCurrentRungVector
              v m probeEnergy broadening disorderStrength hbar pMax)
            hregular)
          inPlaneLadderBareXSource) := by
  rw [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector_x,
    finiteCutoffContinuumBornDysonLadderSolvedVector,
    inPlaneLadderSolvedVector_eq_resummedLadderVertex _ hregular]

@[simp]
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_zero_disorder
    (source : Fin 2) (e v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
      source e v m probeEnergy broadening 0 hbar pMax = currentOperator source e v := by
  fin_cases source <;>
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector,
      inPlaneCurrentOperator, Matrix.transpose, inPlaneRotationMatrix,
      inPlaneLadderBareXSource, inPlaneCoefficientVector]

/-! ## Fixed-disorder zero-broadening insertion -/

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
  have hInsertion : Continuous fun coefficients : InPlaneCoefficientVector =>
      inPlaneCurrentOperator e regime.v (Matrix.transpose (inPlaneRotationMatrix coefficients) source) := by
    apply (continuous_inPlaneCurrentOperator e regime.v).comp
    refine continuous_pi fun direction => ?_
    exact (continuous_apply source).comp
      ((continuous_apply direction).comp continuous_inPlaneRotationMatrix)
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperatorZeroBroadeningBoundary
  exact (hInsertion.tendsto _).comp hSolved

/-! ## Reduced longitudinal insertion -/

/-- Diagonal finite-`η` ladder factor used by reduced crossed current insertions.

This is `(1 - A)⁻¹` for the longitudinal source-`x` rung. It is intentionally separate from the
full two-component dressed current insertion above.
-/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedLongitudinalCurrentFactor
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (1 - finiteCutoffContinuumBornDysonCurrentRungVector
    v m probeEnergy broadening disorderStrength hbar pMax 0)⁻¹

@[simp]
theorem finiteCutoffContinuumBornDysonRetardedAdvancedLongitudinalCurrentFactor_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedLongitudinalCurrentFactor
      v m probeEnergy broadening 0 hbar pMax = 1 := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedLongitudinalCurrentFactor,
    finiteCutoffContinuumBornDysonCurrentRungVector]

end

end QuantumTheory.Models.MassiveDirac
