import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson longitudinal Středa conductivity

This module is the conductivity-level consumer of the finite-cutoff finite-external-broadening
Born-Dyson propagator and solved in-plane retarded-advanced current vertex. The measured current is
the bare physical longitudinal current `jₓ`. Only the RA source vertex is dressed, because the
existing non-crossing ladder solves `Gᴿ Γ Gᴬ`; the explicit RR/AA same-side remainder therefore keeps
the bare `jₓ` source rather than assuming an unproved same-side Bethe–Salpeter dressing.

The pointwise trace is integrated over the physical two-dimensional momentum measure in polar
coordinates. The Bastin/Středa trace prefactor and `d²p/(2πℏ)²` measure are each attached exactly
once. No disorder, broadening, ultraviolet, thermodynamic, or simultaneous limit is taken here, and
the Born-Dyson candidate is not identified with an exact disorder average.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport
open scoped Interval

/-- Pointwise finite-cutoff finite-`η` longitudinal Středa surface bridge. The RA block uses the
solved in-plane source current, while the same-side RR/AA remainder retains the bare longitudinal
source. -/
noncomputable def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceTraceBridge
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  retardedAdvancedVertexTraceKernel
      (currentOperator .x e v)
      (finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
      (inPlaneCurrentOperator e v
        (finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
          v m probeEnergy broadening disorderStrength hbar pMax))
      (finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) -
    sameSideVertexTraceRemainder
      (currentOperator .x e v)
      (currentOperator .x e v)
      (finiteCutoffContinuumBornDysonGreenOperator
        .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonGreenOperator
        .advanced v m px py probeEnergy broadening disorderStrength hbar pMax)

/-- The finite-`η` longitudinal bridge is exactly its RA-dressed block minus the bare-source
same-side RR/AA remainder. -/
theorem finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceTraceBridge_eq_ra_sub_sameSide
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceTraceBridge
        e v m px py probeEnergy broadening disorderStrength hbar pMax =
      retardedAdvancedVertexTraceKernel
          (currentOperator .x e v)
          (finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
          (inPlaneCurrentOperator e v
            (finiteCutoffContinuumBornDysonLadderSolvedXCoefficient
              v m probeEnergy broadening disorderStrength hbar pMax)
            (finiteCutoffContinuumBornDysonLadderSolvedYCoefficient
              v m probeEnergy broadening disorderStrength hbar pMax))
          (finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) -
        sameSideVertexTraceRemainder
          (currentOperator .x e v)
          (currentOperator .x e v)
          (finiteCutoffContinuumBornDysonGreenOperator
            .retarded v m px py probeEnergy broadening disorderStrength hbar pMax)
          (finiteCutoffContinuumBornDysonGreenOperator
            .advanced v m px py probeEnergy broadening disorderStrength hbar pMax) := by
  rfl

/-- At zero disorder and positive external broadening, the RA-dressed/bare-same-side longitudinal
bridge reduces exactly to the clean massive-Dirac `jₓ-jₓ` Středa surface primitive. -/
@[simp]
theorem finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceTraceBridge_zero_disorder
    (e v m px py probeEnergy broadening hbar pMax : ℝ)
    (hbroadening : 0 < broadening) :
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceTraceBridge
        e v m px py probeEnergy broadening 0 hbar pMax =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator v m px py)
        (currentOperator .x e v)
        (currentOperator .x e v)
        probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceTraceBridge
  simp only [finiteCutoffContinuumBornDysonLadderSolvedXCoefficient_zero_disorder,
    finiteCutoffContinuumBornDysonLadderSolvedYCoefficient_zero_disorder,
    finiteCutoffContinuumBornDysonGreenOperator_zero_disorder]
  simp only [inPlaneCurrentOperator, one_smul, zero_smul, add_zero]
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
      (currentOperator .x e v)
      probeEnergy broadening)

/-- Full polar-angle integral of the finite-`η` RA-dressed longitudinal Středa surface trace at
fixed radial momentum. -/
noncomputable def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceAngularTraceIntegral
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceTraceBridge
      e v m (p * Real.cos θ) (p * Real.sin θ)
      probeEnergy broadening disorderStrength hbar pMax

/-- Radial integrand after the full polar-angle integral, including exactly one polar Jacobian
factor `p`. -/
def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceRadialIntegrand
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (p : ℂ) *
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceAngularTraceIntegral
      e v m p probeEnergy broadening disorderStrength hbar pMax

/-- Finite-cutoff polar momentum integral of the finite-`η` RA-dressed longitudinal surface response
before the common Bastin/Středa trace prefactor and physical momentum-measure prefactor are
attached. -/
noncomputable def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceRadialIntegrand
      e v m p probeEnergy broadening disorderStrength hbar pMax

/-- Physically normalized finite-cutoff finite-`η` longitudinal Středa surface conductivity bridge.
The explicit angle integral already supplies the angular measure, so the physical momentum measure
is attached without an extra `2π` factor. This is the finite-`η` conductivity-level insertion needed
before any separately justified weak-disorder or zero-broadening recovery of the RTA benchmark. -/
noncomputable def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral
      e v m probeEnergy broadening disorderStrength hbar pMax

/-- With zero radial cutoff, the physically normalized longitudinal surface conductivity bridge
vanishes exactly. -/
@[simp]
theorem finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge_zero_cutoff
    (e v m probeEnergy broadening disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge
      e v m probeEnergy broadening disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge,
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral]

end

end QuantumTheory.Transport.Models.MassiveDirac
