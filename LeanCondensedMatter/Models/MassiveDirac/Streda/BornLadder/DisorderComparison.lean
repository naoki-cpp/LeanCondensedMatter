import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.TraceBridge
import LeanCondensedMatter.Transport.Disorder.TraceBridge
import LeanCondensedMatter.Transport.Disorder.TraceNormBound
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Exact finite disorder versus the massive-Dirac Born-Dyson RA surface candidate

This comparison uses an *arbitrary* exact finite disorder ensemble on the Dirac Hilbert space
and the existing pointwise finite-cutoff Born-Dyson propagators and RA ladder vertex.

It exposes the difference between the exact ensemble-averaged two-Green RA trace and the
model's RA-dressed/bare-same-side surface trace. There are three independent residuals:
left/right mean-Green mismatch, connected two-Green vertex mismatch, and the bare same-side
RR/AA remainder. The finite ensemble is NOT claimed to realize the model's continuum scalar
impurity law or self-consistent Born closure; controlling these residuals is further work.

This is pointwise in momentum and regulated energy. No conductivity, Fermi-sea, contact,
momentum integration, or weak-disorder/zero-broadening limit is identified.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

variable {Ω : Type*} [Fintype Ω]
variable (ensemble : FiniteDisorderEnsemble (H := DiracHilbert) (Ω := Ω))

/-- Exact pointwise difference from the model's RA-dressed, bare-same-side Středa surface
candidate. The last term is the explicitly retained same-side remainder, not an additional
vertex correction. The remaining trace isolates independent one-particle and connected
two-particle approximation errors without assuming their smallness. -/
theorem averagedTwoGreenTrace_sub_bornDysonSurface_eq_residuals
    (measured source : Fin 2)
    (e v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    let measuredCurrent := currentOperator measured e v
    let sourceCurrent := currentOperator source e v
    let retarded := finiteCutoffContinuumBornDysonGreenOperator
      .retarded v m px py probeEnergy broadening disorderStrength hbar pMax
    let advanced := finiteCutoffContinuumBornDysonGreenOperator
      .advanced v m px py probeEnergy broadening disorderStrength hbar pMax
    let dressed := finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
      source e v m probeEnergy broadening disorderStrength hbar pMax
    ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        probeEnergy broadening probeEnergy (-broadening)
        measuredCurrent sourceCurrent -
      finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
        measured source e v m px py probeEnergy broadening disorderStrength hbar pMax =
      ContinuousLinearMap.finiteDimensionalOperatorTrace
        (measuredCurrent *
          ((ensemble.averagedGreenOfRegulator probeEnergy broadening -
              retarded) * sourceCurrent *
                ensemble.averagedGreenOfRegulator probeEnergy (-broadening) +
            retarded * sourceCurrent *
              (ensemble.averagedGreenOfRegulator probeEnergy (-broadening) - advanced) +
            ensemble.connectedTwoGreenInsertionOfRegulators
              probeEnergy broadening probeEnergy (-broadening) sourceCurrent -
            retarded * (dressed - sourceCurrent) * advanced)) +
      sameSideVertexTraceRemainder measuredCurrent sourceCurrent retarded advanced := by
  dsimp only
  let measuredCurrent := currentOperator measured e v
  let sourceCurrent := currentOperator source e v
  let retarded := finiteCutoffContinuumBornDysonGreenOperator
    .retarded v m px py probeEnergy broadening disorderStrength hbar pMax
  let advanced := finiteCutoffContinuumBornDysonGreenOperator
    .advanced v m px py probeEnergy broadening disorderStrength hbar pMax
  let dressed := finiteCutoffContinuumBornDysonRetardedAdvancedDressedSourceCurrentOperator
    source e v m probeEnergy broadening disorderStrength hbar pMax
  have hRA :=
    ensemble.averagedTwoGreenVertexTraceKernelOfRegulators_sub_dressed_eq
      probeEnergy broadening probeEnergy (-broadening)
      measuredCurrent sourceCurrent retarded dressed advanced
  change
    ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        probeEnergy broadening probeEnergy (-broadening)
        measuredCurrent sourceCurrent -
      (retardedAdvancedVertexTraceKernel measuredCurrent retarded dressed advanced -
        sameSideVertexTraceRemainder measuredCurrent sourceCurrent retarded advanced) =
      ContinuousLinearMap.finiteDimensionalOperatorTrace
        (measuredCurrent *
          ((ensemble.averagedGreenOfRegulator probeEnergy broadening -
              retarded) * sourceCurrent *
                ensemble.averagedGreenOfRegulator probeEnergy (-broadening) +
            retarded * sourceCurrent *
              (ensemble.averagedGreenOfRegulator probeEnergy (-broadening) - advanced) +
            ensemble.connectedTwoGreenInsertionOfRegulators
              probeEnergy broadening probeEnergy (-broadening) sourceCurrent -
            retarded * (dressed - sourceCurrent) * advanced)) +
      sameSideVertexTraceRemainder measuredCurrent sourceCurrent retarded advanced
  calc
    _ = (ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
          probeEnergy broadening probeEnergy (-broadening)
          measuredCurrent sourceCurrent -
        retardedAdvancedVertexTraceKernel measuredCurrent retarded dressed advanced) +
        sameSideVertexTraceRemainder measuredCurrent sourceCurrent retarded advanced := by
          ring
    _ = _ := by rw [hRA]

/-- In the two-component massive-Dirac Hilbert space, the exact disorder-connected
Hall-current trace (x-measured, y-sourced) is quadratically bounded at opposite nonzero
signed regulators. The factor two is the physical orbital/spinor-space dimension, not a
momentum-volume normalization. The comparator uses *exact mean* propagators, not supplied
Born-Dyson Green operators or dressed vertices. -/
theorem norm_averagedHallCurrentTrace_sub_meanProduct_le_uniformPotential_sq
    (e v energy broadening potentialBound : ℝ)
    (hbroadening : broadening ≠ 0) (hbound : 0 ≤ potentialBound)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.averagedTwoGreenVertexTraceKernelOfRegulators
        energy broadening energy (-broadening)
        (currentOperator 0 e v) (currentOperator 1 e v) -
      twoGreenVertexTraceKernel (currentOperator 0 e v)
        (ensemble.averagedGreenOfRegulator energy broadening)
        (currentOperator 1 e v)
        (ensemble.averagedGreenOfRegulator energy (-broadening))‖ ≤
      (2 * ‖currentOperator 0 e v‖) *
        ((2 * (|broadening|⁻¹) ^ 2 * potentialBound) *
          ‖currentOperator 1 e v‖ *
          (2 * (|broadening|⁻¹) ^ 2 * potentialBound)) := by
  have hrank : Module.finrank ℂ DiracHilbert = 2 := by
    simp [DiracHilbert]
  have hboundTrace :=
    ensemble.norm_averagedTwoGreenTrace_sub_meanProduct_le_uniformPotential_sq
      energy broadening energy (-broadening) hbroadening
      (by simpa using hbroadening)
      (currentOperator 0 e v) (currentOperator 1 e v)
      potentialBound hbound hpotential
  simpa only [hrank, Nat.cast_ofNat, abs_neg] using hboundTrace

end

end QuantumTheory.Models.MassiveDirac
