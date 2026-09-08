import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator.Basic
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson RA-dressed Středa surface bridge

This module inserts the solved finite-cutoff finite-external-broadening Born-Dyson current-vertex
coefficients into the retarded-advanced block of the massive-Dirac Středa surface algebra. The
measured current is fixed to the physical `jₓ`, while the bare source direction is indexed by
`Direction2`.

The canonical ladder solution is stored for a bare `σₓ` source as `(α, β)`. Rotational closure
therefore supplies the source-indexed algebraic vertex

```text
Γₓᴿᴬ =  α σₓ + β σᵧ,
Γᵧᴿᴬ = -β σₓ + α σᵧ.
```

These computational values are total; ladder regularity is needed only when the solved coefficient
pair is interpreted as the physical fixed point. Only the `Gᴿ Γ Gᴬ` ladder has been solved. The
explicit same-side RR/AA remainder consequently retains the bare source current rather than reusing
the RA-dressed vertex without a corresponding RR/AA Bethe–Salpeter derivation. The resulting object
is an RA-dressed/bare-same-side bridge, not a claim that the full finite-disorder Středa surface
primitive has been dressed. No momentum integral, conductivity prefactor, disorder/broadening limit,
or exact disorder-average claim is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Retarded-advanced source current obtained by rotating the solved bare-`σₓ` ladder coefficient
pair into the requested in-plane source direction. This is the total algebraic value; the separate
ladder-regularity predicate governs when the coefficient pair is the physical fixed-point solution. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    (source : Direction2)
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  let alpha := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
    .x v m probeEnergy broadening disorderStrength hbar pMax
  let beta := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
    .y v m probeEnergy broadening disorderStrength hbar pMax
  inPlaneCurrentOperator e v
    (inPlaneRotationCoefficient alpha beta .x source)
    (inPlaneRotationCoefficient alpha beta .y source)

/-- The source-indexed retarded-advanced dressed current is electron charge times the Dirac
velocity multiplying the correspondingly rotated solved dimensionless coefficient pair. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_eq_chargeVelocity_smul
    (source : Direction2)
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
        source e v m probeEnergy broadening disorderStrength hbar pMax =
      let alpha := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
        .x v m probeEnergy broadening disorderStrength hbar pMax
      let beta := finiteCutoffContinuumBornDysonLadderSolvedCoefficient
        .y v m probeEnergy broadening disorderStrength hbar pMax
      ((((-e : ℝ) : ℂ)) * (((v : ℝ) : ℂ))) •
        inPlanePauliVertexOperator
          (inPlaneRotationCoefficient alpha beta .x source)
          (inPlaneRotationCoefficient alpha beta .y source) := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
  rw [inPlaneCurrentOperator_eq_chargeVelocity_smul_inPlanePauliVertexOperator]

@[simp]
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_zero_disorder
    (source : Direction2) (e v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
      source e v m probeEnergy broadening 0 hbar pMax = currentOperator source e v := by
  cases source <;>
    simp [finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator,
      inPlaneCurrentOperator, inPlaneRotationCoefficient]

/-- Pointwise finite-cutoff finite-`η` Středa surface bridge with a bare measured `jₓ`, the solved
source-indexed algebraic vertex only in the RA block, and the corresponding bare source current in
the RR/AA same-side remainder. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
    (source : Direction2)
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  retardedAdvancedVertexTraceKernel
      (currentOperator .x e v)
      (finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
        source e v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) -
    sameSideVertexTraceRemainder
      (currentOperator .x e v)
      (currentOperator source e v)
      (finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m px py probeEnergy broadening disorderStrength hbar pMax)

/-- At zero disorder and positive external broadening, the source-indexed RA-dressed/bare-same-side
bridge reduces exactly to the clean massive-Dirac `jₓ-j_source` Středa surface primitive. -/
@[simp]
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge_zero_disorder
    (source : Direction2)
    (e v m px py probeEnergy broadening hbar pMax : ℝ)
    (hbroadening : 0 < broadening) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
        source e v m px py probeEnergy broadening 0 hbar pMax =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentOperator .x e v)
        (currentOperator source e v)
        probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
  simp only [
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator_zero_disorder,
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
      (currentOperator source e v)
      probeEnergy broadening)

end

end QuantumTheory.Transport.Models.MassiveDirac
