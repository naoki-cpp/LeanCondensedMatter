import LeanCondensedMatter.Models.MassiveDirac.Model.OperatorSpectral
import LeanCondensedMatter.Models.MassiveDirac.Model.Berry.Bridge
import LeanCondensedMatter.Transport.Streda.FiniteProjectorBastin

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

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open BerryGeometry
open ContinuousLinearMap

/-- An opposite-band ordered current block is exactly `e²` times the gauge-independent force-matrix
numerator. -/
theorem currentBandBlockTrace_interband_eq_chargeSq_forceMatrixTraceNumerator
    (μ ν : Fin 2) (band : Band) (e v m px py : ℝ) :
    currentBandBlockTrace μ ν band (oppositeBand band) e v m px py =
      (((e ^ 2 : ℝ) : ℂ)) * forceMatrixTraceNumerator μ ν band v m px py := by
  have htrace := finiteDimensionalOperatorTrace_two_smul_toEuclideanCLM
    (bandProjector (oppositeBand band) v m px py)
    (bandProjector band v m px py)
    (velocity μ v) (velocity ν v) (((-e : ℝ) : ℂ))
  simpa [currentBandBlockTrace, bandProjectorOperator, currentOperator,
    matrixOperator, current, forceMatrixTraceNumerator, neg_sq] using htrace

/-- Normalizing the Hall interband current block by the squared interband gap reproduces
`e²` times the generic pointwise Berry curvature. This is the transport consumer of the canonical
Massive-Dirac spectral bridge. -/
theorem two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_pointwiseBerryCurvature
    (band : Band) (e v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    2 * (currentBandBlockTrace 0 1 band (oppositeBand band) e v m px py).im /
        interbandEnergyGap band v m px py ^ 2 =
      e ^ 2 * (pointwiseEigenbasisData v m px py hE).berryCurvature 0 1 band := by
  rw [currentBandBlockTrace_interband_eq_chargeSq_forceMatrixTraceNumerator 0 1]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [pointwiseBerryCurvature_xy_eq_forceMatrixBerryCurvature band v m px py hE]
  unfold forceMatrixBerryCurvature
  ring

/-- Bastin operator integrand with the generic Green operators replaced by their exact massive-Dirac
projector expansions. -/
noncomputable def projectorBastinOperatorIntegrand
    (e v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  bastinOperatorKernelFromPropagators
    (currentOperator 0 e v) (currentOperator 1 e v)
    (projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py)
    (projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py)

/-- Ordinary trace of the projector-expanded Bastin operator kernel. -/
noncomputable def projectorBastinTraceIntegrand
    (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (projectorBastinOperatorIntegrand e v m px py probeEnergy broadening)

/-- At nonzero broadening and away from the band degeneracy, the generic massive-Dirac Bastin trace
integrand is exactly the projector-expanded expression. -/
theorem regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : broadening ≠ 0) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator 0 e v) (currentOperator 1 e v) probeEnergy broadening =
      projectorBastinTraceIntegrand e v m px py probeEnergy broadening := by
  simpa only [projectorBastinTraceIntegrand,
    projectorBastinOperatorIntegrand, bastinOperatorKernelFromPropagators,
    projectorResolvent] using
    (QuantumTheory.Transport.regularizedBastinTraceIntegrand_eq_projectorSum
      (hamiltonianOperator v m px py) (hamiltonianOperator_isSelfAdjoint v m px py)
      (fun band : Band => bandProjectorOperator band v m px py)
      (fun band : Band => bandEnergy band v m px py)
      (bandProjectorOperator_completeOrthogonalIdempotents v m px py hE).complete
      (fun band : Band => hamiltonianOperator_mul_bandProjectorOperator band v m px py hE)
      (currentOperator 0 e v) (currentOperator 1 e v)
      probeEnergy broadening hbroadening)

end

end QuantumTheory.Models.MassiveDirac
