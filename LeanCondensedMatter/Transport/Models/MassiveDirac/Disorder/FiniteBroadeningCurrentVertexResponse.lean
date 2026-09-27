import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
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

No Streda trace, Gaussian-crossed Fourier kernel, same-side remainder, conductivity normalization,
or zero-broadening limit is owned here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-! ## Source-indexed response insertion -/

/-- Source-indexed finite-cutoff finite-`η` Born-Dyson dressed in-plane coefficient vector. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
    (source : Fin 2)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : InPlaneCoefficientVector :=
  Matrix.transpose (inPlaneRotationMatrix
    (finiteCutoffContinuumBornDysonLadderSolvedVector
      v m probeEnergy broadening disorderStrength hbar pMax)) source

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
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentCoefficientVector
  unfold finiteCutoffContinuumBornDysonLadderSolvedVector
  rw [inPlaneLadderSolvedVector_eq_resummedLadderVertex
    (finiteCutoffContinuumBornDysonCurrentRungVector
      v m probeEnergy broadening disorderStrength hbar pMax)
    hregular]
  congr 1
  funext direction
  fin_cases direction <;> simp [Matrix.transpose, inPlaneRotationMatrix]

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

end QuantumTheory.Transport.Models.MassiveDirac
