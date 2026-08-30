import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexLadder
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Longitudinal.FiniteBroadening
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson Hall Středa surface channel

This module inserts the solved finite-cutoff finite-external-broadening Born-Dyson current vertex
into the massive-Dirac Hall Středa surface channel.

The repository Hall convention keeps the measured current bare along `x` and dresses the source
current that is bare along `y`.  Since the canonical ladder solution is stored for a bare `σₓ`
source as `(α, β)`, rotational closure fixes the dressed Hall source to

```text
Γᵧ = -β σₓ + α σᵧ.
```

At finite broadening the supplied-Green Středa surface kernel retains the exact same-side RR/AA
remainder.  No same-side term, momentum integral, conductivity prefactor, disorder/broadening limit,
or exact disorder-average claim is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Physical Hall source current obtained by inserting the rotated solved coefficient pair
`(-β, α)` into the existing in-plane dressed-current boundary. -/
noncomputable def finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  dressedLongitudinalCurrentOperator e v
    (-finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- The physical Hall source is electron charge times the Dirac velocity multiplying the rotated
solved dimensionless transverse vertex. -/
theorem finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator_eq_chargeVelocity_smul
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator
        e v m probeEnergy broadening disorderStrength hbar pMax =
      (((-e * v : ℝ) : ℂ)) •
        finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex
          v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator
  rw [dressedLongitudinalCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
  rfl

@[simp] theorem finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator_zero_disorder
    (e v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator
      e v m probeEnergy broadening 0 hbar pMax = currentOperator .y e v := by
  simp [finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator]

/-- Pointwise finite-cutoff finite-`η` Born-Dyson Hall Středa surface primitive trace kernel.  The
measured current is bare `jₓ`, the source is the solved dressed `jᵧ`, and the finite-`η` Born-Dyson
Green pair is supplied explicitly. -/
noncomputable def finiteCutoffContinuumBornDysonHallStredaSurfacePrimitiveTraceKernel
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  suppliedGreenStredaSurfacePrimitiveTraceKernel
    (currentOperator .x e v)
    (finiteCutoffContinuumBornDysonGreenOperator
      .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator
      e v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonGreenOperator
      .advanced v m px py probeEnergy broadening disorderStrength hbar pMax)

/-- The finite-`η` Hall surface kernel keeps the RA block and explicit same-side RR/AA remainder
separate. -/
theorem finiteCutoffContinuumBornDysonHallStredaSurfacePrimitiveTraceKernel_eq_ra_sub_sameSide
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonHallStredaSurfacePrimitiveTraceKernel
        e v m px py probeEnergy broadening disorderStrength hbar pMax =
      retardedAdvancedVertexTraceKernel
          (currentOperator .x e v)
          (finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator
            e v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) -
        sameSideVertexTraceRemainder
          (currentOperator .x e v)
          (finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator
            e v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) := by
  rfl

/-- At zero disorder and positive external broadening, the finite-Born-Dyson Hall surface kernel
reduces exactly to the clean massive-Dirac `jₓ-jᵧ` Středa surface primitive. -/
@[simp] theorem finiteCutoffContinuumBornDysonHallStredaSurfacePrimitiveTraceKernel_zero_disorder
    (e v m px py probeEnergy broadening hbar pMax : ℝ)
    (hbroadening : 0 < broadening) :
    finiteCutoffContinuumBornDysonHallStredaSurfacePrimitiveTraceKernel
        e v m px py probeEnergy broadening 0 hbar pMax =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentOperator .x e v)
        (currentOperator .y e v)
        probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonHallStredaSurfacePrimitiveTraceKernel
  simp only [finiteCutoffContinuumBornDysonDressedHallSourceCurrentOperator_zero_disorder,
    finiteCutoffContinuumBornDysonGreenOperator_zero_disorder]
  rw [← retardedResolvent_eq_pauliGreenOperator
      v m px py probeEnergy broadening hbroadening]
  rw [← advancedResolvent_eq_pauliGreenOperator
      v m px py probeEnergy broadening hbroadening]
  symm
  exact regularizedStredaSurfacePrimitiveTrace_eq_suppliedGreen
    (hamiltonianOperator v m px py)
    (currentOperator .x e v)
    (currentOperator .y e v)
    probeEnergy broadening

end

end AnomalousHall.MassiveDirac
