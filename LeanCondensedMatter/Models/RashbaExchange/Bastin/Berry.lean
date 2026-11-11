import LeanCondensedMatter.Models.RashbaExchange.Model.OperatorSpectral
import LeanCondensedMatter.Models.RashbaExchange.Current
import LeanCondensedMatter.Models.RashbaExchange.Model.Interband
import LeanCondensedMatter.Transport.Streda.FiniteProjectorBastin

set_option linter.style.header false

/-!
# Rashba-exchange Bastin projector blocks and Berry curvature

The finite-broadening Bastin kernel and the clean Berry-curvature layer are connected through the
same gauge-free two-band projectors.  The physical current is `j = q v`, so every interband
current block carries the explicit factor `q²`.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open ContinuousLinearMap
open QuantumTheory.Transport

/-- An opposite-band ordered current block is `q²` times the gauge-independent velocity
force-matrix numerator. -/
theorem currentBandBlockTrace_interband_eq_chargeSq_forceMatrixTraceNumerator
    (params : Parameters) (μ ν : Fin 2) (band : Band) (px py : ℝ) :
    currentBandBlockTrace params μ ν band (oppositeBand band) px py =
      (((params.signedCharge ^ 2 : ℝ) : ℂ)) *
        forceMatrixTraceNumerator params μ ν band px py := by
  have htrace := finiteDimensionalOperatorTrace_two_smul_toEuclideanCLM
    (bandProjector params (oppositeBand band) px py)
    (bandProjector params band px py)
    (velocityOperator params μ px py) (velocityOperator params ν px py)
    (((params.signedCharge : ℝ) : ℂ))
  simpa [currentBandBlockTrace, bandProjectorOperator, currentBoundedOperator,
    currentOperator, matrixOperator, forceMatrixTraceNumerator] using htrace

/-- Normalizing the interband current block by the squared energy gap reproduces `q²` times the
closed Rashba-exchange Berry curvature. -/
theorem two_mul_currentBandBlockTrace_interband_im_div_gap_sq_eq_chargeSq_berryCurvature
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    2 * (currentBandBlockTrace params 0 1 band (oppositeBand band) px py).im /
        interbandEnergyGap params band px py ^ 2 =
      params.signedCharge ^ 2 * berryCurvature params band px py := by
  rw [currentBandBlockTrace_interband_eq_chargeSq_forceMatrixTraceNumerator
    params 0 1]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [← forceMatrixBerryCurvature_eq_berryCurvature params band px py hE]
  unfold forceMatrixBerryCurvature
  ring

/-- Bastin operator integrand with canonical Green operators replaced by exact projector
resolvents. -/
noncomputable def projectorBastinOperatorIntegrand
    (params : Parameters) (px py probeEnergy broadening : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  let retarded :=
    projectorResolvent
      (retardedSpectralParameter probeEnergy broadening) params px py
  let advanced :=
    projectorResolvent
      (advancedSpectralParameter probeEnergy broadening) params px py
  (currentBoundedOperator params 0 px py * retarded ^ 2 *
      currentBoundedOperator params 1 px py -
    currentBoundedOperator params 1 px py * advanced ^ 2 *
      currentBoundedOperator params 0 px py) *
    (retarded - advanced)

/-- Ordinary trace of the projector-expanded Bastin kernel. -/
noncomputable def projectorBastinTraceIntegrand
    (params : Parameters) (px py probeEnergy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (projectorBastinOperatorIntegrand params px py probeEnergy broadening)

/-- At nonzero broadening and away from the band degeneracy, the generic Bastin trace is exactly the
projector-expanded Rashba-exchange expression. -/
theorem regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : broadening ≠ 0) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator params px py)
        (currentBoundedOperator params 0 px py)
        (currentBoundedOperator params 1 px py)
        probeEnergy broadening =
      projectorBastinTraceIntegrand params px py probeEnergy broadening := by
  simpa only [projectorBastinTraceIntegrand,
    projectorBastinOperatorIntegrand, projectorResolvent] using
    (QuantumTheory.Transport.regularizedBastinTraceIntegrand_eq_projectorSum
      (hamiltonianOperator params px py) (hamiltonianOperator_isSelfAdjoint params px py)
      (fun band : Band => bandProjectorOperator params band px py)
      (fun band : Band => bandEnergy params band px py)
      (bandProjectorOperator_completeOrthogonalIdempotents params px py hE).complete
      (fun band : Band => hamiltonianOperator_mul_bandProjectorOperator params band px py hE)
      (currentBoundedOperator params 0 px py) (currentBoundedOperator params 1 px py)
      probeEnergy broadening hbroadening)

end

end QuantumTheory.Models.RashbaExchange
