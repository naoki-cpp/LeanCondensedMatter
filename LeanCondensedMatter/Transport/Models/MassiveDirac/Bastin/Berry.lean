import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Bridge
import LeanCondensedMatter.Transport.Streda.TraceKernel

set_option linter.style.header false

/-!
# Massive-Dirac Bastin projector blocks and Berry curvature

The finite-broadening Kubo–Bastin layer and the clean Berry-curvature layer share the same
massive-Dirac spectral projectors. The model layer owns the direction-indexed ordered current band
block

```text
Tr(P_target j_μ P_source j_ν).
```

For an interband pair with `target = oppositeBand source`, the current vertices are exactly
`j_μ = -e v_μ`, so that canonical block is `e²` times the force-matrix numerator. For the Hall
component `(μ,ν) = (x,y)`, its normalized imaginary part is therefore directly `e²` times the clean
Berry curvature.

This file also replaces the generic retarded/advanced resolvents in the finite-broadening Bastin
integrand by the exact projector resolvents owned by `MassiveDirac/Model/OperatorSpectral`. The
subsequent band decomposition, occupation integration, and zero-broadening analysis remain
downstream.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- An opposite-band ordered current block is exactly `e²` times the gauge-independent force-matrix
numerator. -/
theorem currentBandBlockTrace_interband_eq_chargeSq_forceMatrixTraceNumerator
    (μ ν : Direction2) (band : Band) (e v m px py : ℝ) :
    currentBandBlockTrace μ ν band (oppositeBand band) e v m px py =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator μ ν band v m px py := by
  unfold currentBandBlockTrace
  calc
    finiteDimensionalOperatorTrace
        (bandProjectorOperator (oppositeBand band) v m px py * currentOperator μ e v *
          bandProjectorOperator band v m px py * currentOperator ν e v) =
      Matrix.trace
        (bandProjector (oppositeBand band) v m px py * current μ e v *
          bandProjector band v m px py * current ν e v) := by
      simpa [bandProjectorOperator, currentOperator, matrixOperator] using
        finiteDimensionalOperatorTrace_toEuclideanCLM
          (bandProjector (oppositeBand band) v m px py * current μ e v *
            bandProjector band v m px py * current ν e v)
    _ = (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator μ ν band v m px py := by
      simp [current, forceMatrixTraceNumerator]
      ring

/-- Normalizing the Hall interband current block by the squared interband gap directly reproduces
`e²` times the clean Berry curvature away from the Dirac degeneracy. -/
theorem two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    2 * (currentBandBlockTrace .x .y band (oppositeBand band) e v m px py).im /
        interbandEnergyGap band v m px py ^ 2 =
      e ^ 2 * berryCurvature band v m px py := by
  rw [currentBandBlockTrace_interband_eq_chargeSq_forceMatrixTraceNumerator .x .y]
  push_cast
  simp only [Complex.mul_im]
  rw [← forceMatrixBerryCurvature_eq_berryCurvature band v m px py hE]
  unfold forceMatrixBerryCurvature
  ring

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

/-- At nonzero broadening and away from the band degeneracy, the generic massive-Dirac Bastin trace
integrand is exactly the projector-expanded expression. -/
theorem regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : broadening ≠ 0) :
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
        v m px py probeEnergy broadening hE hbroadening
  have hadvanced :
      advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py := by
    simpa only [advancedResolvent, advancedSpectralParameter,
      spectralResolvent_advanced_ofRegulator, spectralParameter_advanced_ofRegulator] using
      resolvent_spectralParameterOfRegulator_eq_projectorResolvent
        v m px py probeEnergy (-broadening) hE
        (neg_ne_zero.mpr hbroadening)
  rw [hretarded, hadvanced]
  congr 1
  noncomm_ring

end

end QuantumTheory.Transport.Models.MassiveDirac
