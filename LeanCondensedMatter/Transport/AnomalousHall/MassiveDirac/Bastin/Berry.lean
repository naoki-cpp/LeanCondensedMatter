import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic.BerryBridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Streda.TraceKernel

set_option linter.style.header false

/-!
# Massive-Dirac Bastin projector blocks and Berry curvature

The finite-broadening Kubo–Bastin layer and the clean Berry-curvature layer now share the same
massive-Dirac spectral projectors. This file makes that common block explicit without choosing an
eigenvector gauge.

First, the generic retarded/advanced resolvents in the Bastin integrand are replaced by the exact
projector resolvents owned by `MassiveDirac/Model/OperatorSpectral`. Second, the direction-indexed
interband operator trace

```text
Tr(P_m j_μ P_n j_ν),  m = oppositeBand n,
```

is transported back to the concrete `2 × 2` matrix trace. For arbitrary in-plane directions, the
current vertices are exactly `j_μ = -e v_μ`, so the trace is `e²` times the corresponding
force-matrix numerator. For the Hall component `(μ,ν) = (x,y)`, dividing its imaginary part by the
squared interband gap reproduces `e² Ω_n`.

This is still a pointwise, finite-dimensional bridge. The next step is to expand the full Bastin
projector expression into its diagonal/interband band blocks and then perform the occupation and
zero-broadening analysis. No such limiting statement is made here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Gauge-independent direction-indexed interband current block in the bounded-operator
representation. -/
noncomputable def interbandCurrentTrace
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator (oppositeBand band) v m px py * currentOperator μ e v *
      bandProjectorOperator band v m px py * currentOperator ν e v)

/-- Replacing the bounded current vertices by the canonical electron-charge velocity
representatives leaves the interband current block unchanged. -/
theorem interbandCurrentTrace_eq_canonicalChargeVelocityTrace
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace μ ν band e v m px py =
      finiteDimensionalOperatorTrace
        (bandProjectorOperator (oppositeBand band) v m px py *
          ((((-e : ℝ) : ℂ)) • velocityOperator μ v) *
          bandProjectorOperator band v m px py *
          ((((-e : ℝ) : ℂ)) • velocityOperator ν v)) := by
  unfold interbandCurrentTrace
  rw [currentOperator_eq_charge_smul_velocityOperator,
    currentOperator_eq_charge_smul_velocityOperator]

/-- The bounded-operator interband current trace is exactly the ordinary matrix trace of the same
projector/current block. -/
theorem interbandCurrentTrace_eq_matrixTrace
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace μ ν band e v m px py =
      Matrix.trace
        (bandProjector (oppositeBand band) v m px py * current μ e v *
          bandProjector band v m px py * current ν e v) := by
  unfold interbandCurrentTrace
  simpa [bandProjectorOperator, currentOperator, matrixOperator] using
    finiteDimensionalOperatorTrace_toEuclideanCLM
      (bandProjector (oppositeBand band) v m px py * current μ e v *
        bandProjector band v m px py * current ν e v)

/-- Replacing direction-indexed charge currents by `-e` times the corresponding velocities pulls
out `e²` from the interband projector trace. -/
theorem matrixInterbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    Matrix.trace
        (bandProjector (oppositeBand band) v m px py * current μ e v *
          bandProjector band v m px py * current ν e v) =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator μ ν band v m px py := by
  simp [current, forceMatrixTraceNumerator]
  ring

/-- Operator form of the same direction-indexed `e²` factorization. -/
theorem interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    interbandCurrentTrace μ ν band e v m px py =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator μ ν band v m px py := by
  rw [interbandCurrentTrace_eq_matrixTrace]
  exact matrixInterbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator
    μ ν band e v m px py

/-- Imaginary part of the physical-current interband Hall block. -/
theorem interbandCurrentTrace_im
    (band : Band) (e v m px py : ℝ) :
    (interbandCurrentTrace .x .y band e v m px py).im =
      e ^ 2 * (forceMatrixTraceNumerator .x .y band v m px py).im := by
  rw [interbandCurrentTrace_eq_chargeSq_forceMatrixTraceNumerator .x .y]
  push_cast
  simp [Complex.mul_im, pow_two]

/-- Berry-curvature combination formed directly from the physical-current Hall interband trace. -/
noncomputable def interbandCurrentBerryWeight
    (band : Band) (e v m px py : ℝ) : ℝ :=
  2 * (interbandCurrentTrace .x .y band e v m px py).im /
    interbandEnergyGap band v m px py ^ 2

/-- The current-current interband Hall block is `e²` times the force-matrix Berry-curvature block. -/
theorem interbandCurrentBerryWeight_eq_chargeSq_forceMatrixBerryCurvature
    (band : Band) (e v m px py : ℝ) :
    interbandCurrentBerryWeight band e v m px py =
      e ^ 2 * forceMatrixBerryCurvature band v m px py := by
  rw [interbandCurrentBerryWeight, interbandCurrentTrace_im]
  unfold forceMatrixBerryCurvature
  ring

/-- Away from the Dirac degeneracy, the physical-current interband block therefore reproduces
`e²` times the clean Berry curvature. -/
theorem interbandCurrentBerryWeight_eq_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    interbandCurrentBerryWeight band e v m px py =
      e ^ 2 * berryCurvature band v m px py := by
  rw [interbandCurrentBerryWeight_eq_chargeSq_forceMatrixBerryCurvature]
  rw [forceMatrixBerryCurvature_eq_berryCurvature band v m px py hE]

/-- Bastin operator integrand with the generic Green operators replaced by their exact massive-Dirac
projector expansions. -/
noncomputable def projectorBastinOperatorIntegrand
    (e v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  let retarded :=
    projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py
  let advanced :=
    projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py
  (currentOperator .x e v * retarded ^ 2 * currentOperator .y e v -
      currentOperator .y e v * advanced ^ 2 * currentOperator .x e v) *
    (retarded - advanced)

/-- Ordinary trace of the projector-expanded Bastin operator kernel. -/
noncomputable def projectorBastinTraceIntegrand
    (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (projectorBastinOperatorIntegrand e v m px py probeEnergy broadening)

/-- The existing Bastin trace integrand is unchanged when its current vertices are rewritten as the
canonical electron-charge velocity representatives. -/
theorem regularizedBastinTraceIntegrand_eq_canonicalChargeVelocityVertices
    (e v m px py probeEnergy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator .x e v) (currentOperator .y e v) probeEnergy broadening =
      regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        ((((-e : ℝ) : ℂ)) • velocityOperator .x v)
        ((((-e : ℝ) : ℂ)) • velocityOperator .y v) probeEnergy broadening := by
  rw [currentOperator_eq_charge_smul_velocityOperator,
    currentOperator_eq_charge_smul_velocityOperator]

/-- At positive broadening and away from the band degeneracy, the generic massive-Dirac Bastin trace
integrand is exactly the projector-expanded expression. -/
theorem regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator .x e v) (currentOperator .y e v) probeEnergy broadening =
      projectorBastinTraceIntegrand e v m px py probeEnergy broadening := by
  unfold regularizedBastinTraceIntegrand projectorBastinTraceIntegrand
    projectorBastinOperatorIntegrand regularizedBastinOperatorIntegrand
    retardedAdvancedResolventDifference
  have hretarded :
      retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py := by
    simpa only [retardedResolvent, retardedSpectralParameter,
      spectralResolvent_retarded_ofRegulator, spectralParameter_retarded_ofRegulator] using
      resolvent_spectralParameterOfRegulator_eq_projectorResolvent
        v m px py probeEnergy broadening hE (ne_of_gt hbroadening)
  have hadvanced :
      advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py := by
    simpa only [advancedResolvent, advancedSpectralParameter,
      spectralResolvent_advanced_ofRegulator, spectralParameter_advanced_ofRegulator] using
      resolvent_spectralParameterOfRegulator_eq_projectorResolvent
        v m px py probeEnergy (-broadening) hE
        (neg_ne_zero.mpr (ne_of_gt hbroadening))
  rw [hretarded, hadvanced]
  congr 1
  noncomm_ring

end

end AnomalousHall.MassiveDirac
