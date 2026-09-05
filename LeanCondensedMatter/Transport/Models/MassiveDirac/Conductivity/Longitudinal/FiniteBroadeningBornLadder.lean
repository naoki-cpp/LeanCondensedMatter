import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator

set_option linter.style.header false

/-!
# Physical finite-broadening Born-Dyson dressed current

This module connects the solved dimensionless finite-`η` Born-Dyson ladder vertex to the model-owned
in-plane physical-current boundary. The ladder algebra and physical current convention remain
owned by their existing modules; this file only composes them.

No Kubo/Středa trace insertion, conductivity theorem, broadening/disorder limit, or exact disorder-
average claim is made here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Physical dressed longitudinal charge current obtained from the solved normalized finite-`η`
Born-Dyson ladder coefficients. -/
noncomputable def finiteCutoffContinuumBornDysonDressedLongitudinalCurrentOperator
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneCurrentOperator e v
    (finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- The physical solved current is electron charge times the Dirac velocity multiplying the solved
dimensionless finite-`η` Born-Dyson Pauli vertex. -/
theorem finiteCutoffContinuumBornDysonDressedLongitudinalCurrentOperator_eq_chargeVelocity_smul
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDressedLongitudinalCurrentOperator
        e v m probeEnergy broadening disorderStrength hbar pMax =
      ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) •
        finiteCutoffContinuumBornDysonLadderSolvedVertex
          v m probeEnergy broadening disorderStrength hbar pMax := by
  rw [finiteCutoffContinuumBornDysonDressedLongitudinalCurrentOperator,
    inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
  rfl

/-- With zero disorder strength, the solved physical finite-`η` current reduces exactly to the bare
longitudinal charge-current operator. -/
@[simp] theorem finiteCutoffContinuumBornDysonDressedLongitudinalCurrentOperator_zero_disorder
    (e v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDressedLongitudinalCurrentOperator
      e v m probeEnergy broadening 0 hbar pMax = currentOperator .x e v := by
  simp [finiteCutoffContinuumBornDysonDressedLongitudinalCurrentOperator, inPlaneCurrentOperator]

end

end QuantumTheory.Transport.Models.MassiveDirac
