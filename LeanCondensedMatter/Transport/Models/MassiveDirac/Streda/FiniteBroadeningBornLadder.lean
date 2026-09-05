import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson RA-dressed Hall Středa surface bridge

This module inserts the solved finite-cutoff finite-external-broadening Born-Dyson current vertex
into only the retarded-advanced block associated with the massive-Dirac Hall Středa surface
algebra.

The repository Hall convention keeps the measured current bare along `x` and dresses the source
current that is bare along `y`.  Since the canonical ladder solution is stored for a bare `σₓ`
source as `(α, β)`, rotational closure fixes the retarded-advanced dressed Hall source to

```text
Γᵧᴿᴬ = -β σₓ + α σᵧ.
```

Only the `Gᴿ Γᵧᴿᴬ Gᴬ` ladder has been solved.  Therefore the explicit same-side RR/AA remainder
retains the bare `jᵧ` source rather than reusing the RA-dressed vertex without a corresponding RR/AA
Bethe–Salpeter derivation.  The resulting object is an RA-dressed/bare-same-side bridge, not a claim
that the full finite-disorder Středa surface primitive has been dressed.  No momentum integral,
conductivity prefactor, disorder/broadening limit, or exact disorder-average claim is introduced
here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Physical retarded-advanced Hall source current obtained by inserting the rotated solved
coefficient pair `(-β, α)` into the model-owned in-plane current boundary. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  inPlaneCurrentOperator e v
    (-finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
      v m probeEnergy broadening disorderStrength hbar pMax)

/-- The physical retarded-advanced Hall source is electron charge times the Dirac velocity
multiplying the rotated solved dimensionless transverse vertex. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator_eq_chargeVelocity_smul
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
        e v m probeEnergy broadening disorderStrength hbar pMax =
      ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) •
        finiteCutoffContinuumBornDysonLadderSolvedTransverseVertex
          v m probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
  rw [inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]
  rfl

@[simp]
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator_zero_disorder
    (e v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
      e v m probeEnergy broadening 0 hbar pMax = currentOperator .y e v := by
  simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator,
    inPlaneCurrentOperator]

/-- Pointwise finite-cutoff finite-`η` Hall bridge with the solved `Γᵧᴿᴬ` only in the RA block and
bare `jᵧ` in the RR/AA same-side remainder.  This deliberately does not identify the result with a
fully dressed finite-disorder Středa surface primitive. -/
noncomputable def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  retardedAdvancedVertexTraceKernel
      (currentOperator .x e v)
      (finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
        e v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) -
    sameSideVertexTraceRemainder
      (currentOperator .x e v)
      (currentOperator .y e v)
      (finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m px py probeEnergy broadening disorderStrength hbar pMax)

/-- The finite-`η` Hall bridge is exactly its RA-dressed block minus the bare-source same-side RR/AA
remainder. -/
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge_eq_ra_sub_sameSide
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge
        e v m px py probeEnergy broadening disorderStrength hbar pMax =
      retardedAdvancedVertexTraceKernel
          (currentOperator .x e v)
          (finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator
            e v m probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) -
        sameSideVertexTraceRemainder
          (currentOperator .x e v)
          (currentOperator .y e v)
          (finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) := by
  rfl

/-- At zero disorder and positive external broadening, the RA-dressed/bare-same-side bridge reduces
exactly to the clean massive-Dirac `jₓ-jᵧ` Středa surface primitive. -/
@[simp]
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge_zero_disorder
    (e v m px py probeEnergy broadening hbar pMax : ℝ)
    (hbroadening : 0 < broadening) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge
        e v m px py probeEnergy broadening 0 hbar pMax =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentOperator .x e v)
        (currentOperator .y e v)
        probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge
  simp only [
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedHallSourceCurrentOperator_zero_disorder,
    finiteCutoffContinuumBornDysonGreenOperator_zero_disorder]
  have hret :
      retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        pauliGreenOperator .retarded v m px py probeEnergy broadening := by
    simpa [retardedResolvent, retardedSpectralParameter, pauliGreenOperator] using
      resolvent_spectralParameterOfRegulator_eq_pauliGreenOperatorOfRegulator
        v m px py probeEnergy broadening (ne_of_gt hbroadening)
  have hadv :
      advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        pauliGreenOperator .advanced v m px py probeEnergy broadening := by
    simpa [advancedResolvent, advancedSpectralParameter, pauliGreenOperator] using
      resolvent_spectralParameterOfRegulator_eq_pauliGreenOperatorOfRegulator
        v m px py probeEnergy (-broadening)
        (neg_ne_zero.mpr (ne_of_gt hbroadening))
  rw [← hret, ← hadv]
  symm
  simpa [suppliedGreenStredaSurfacePrimitiveTraceKernel] using
    (regularizedStredaSurfacePrimitiveTrace_eq_suppliedGreen
      (hamiltonianOperator v m px py)
      (currentOperator .x e v)
      (currentOperator .y e v)
      probeEnergy broadening)

end

end AnomalousHall.MassiveDirac
