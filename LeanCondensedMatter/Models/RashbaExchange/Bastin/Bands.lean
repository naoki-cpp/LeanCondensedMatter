import LeanCondensedMatter.Models.RashbaExchange.Bastin.Berry
import LeanCondensedMatter.Transport.Streda.InterbandPole

set_option linter.style.header false

/-!
# Rashba-exchange finite-broadening Bastin band-pair decomposition

The finite-projector Bastin trace is an exact ordered sum over source and
target bands. The diagonal sector is retained at nonzero broadening; no
clean-limit or momentum-integral interchange is asserted here. The scalar
kinetic-energy shift remains explicit through the Rashba band energies.
At zero broadening, the algebraic coefficient uses Lean's totalized complex
inverse and is not the physical one-sided zero-broadening limit.
Finite-window integrals and Hall-response bridges are owned downstream by
`Bastin/ResponseBridge.lean`.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport
open ContinuousLinearMap

/-- Contribution from one ordered source/target band pair and two current
directions. The reversed current ordering remains part of the same block. -/
noncomputable def bastinBandPairContribution
    (params : Parameters) (μ ν : Fin 2) (source target : Band)
    (px py probeEnergy broadening : ℝ) : ℂ :=
  let r := scalarResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening)
    (bandEnergy params source px py)
  let a := scalarResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening)
    (bandEnergy params source px py)
  let d := scalarSpectralDifferenceCoefficient
    (bandEnergy params target px py) probeEnergy broadening
  r ^ 2 * d * currentBandBlockTrace params μ ν source target px py -
    a ^ 2 * d * currentBandBlockTrace params ν μ source target px py

/-- Both diagonal band pairs of the finite-broadening Hall trace. -/
noncomputable def diagonalBastinTraceContribution
    (params : Parameters) (px py probeEnergy broadening : ℝ) : ℂ :=
  ∑ band : Band,
    bastinBandPairContribution params 0 1 band band px py probeEnergy broadening

/-- Both ordered interband pairs of the finite-broadening Hall trace. -/
noncomputable def interbandBastinTraceContribution
    (params : Parameters) (px py probeEnergy broadening : ℝ) : ℂ :=
  ∑ band : Band,
    bastinBandPairContribution params 0 1 band (oppositeBand band)
      px py probeEnergy broadening

/-- Direction-indexed finite-projector Bastin trace; the public Hall-oriented
projector trace is its specialization to currents `(0, 1)`. -/
noncomputable def projectorBastinTraceIntegrandFor
    (params : Parameters) (μ ν : Fin 2)
    (px py probeEnergy broadening : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bastinOperatorKernelFromPropagators
      (currentBoundedOperator params μ px py)
      (currentBoundedOperator params ν px py)
      (projectorResolvent (retardedSpectralParameter probeEnergy broadening) params px py)
      (projectorResolvent (advancedSpectralParameter probeEnergy broadening) params px py))

/-- Exact ordered source/target band-pair expansion for arbitrary current directions. -/
theorem projectorBastinTraceIntegrandFor_eq_band_sum
    (params : Parameters) (μ ν : Fin 2) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    projectorBastinTraceIntegrandFor params μ ν px py probeEnergy broadening =
      ∑ source : Band, ∑ target : Band,
        bastinBandPairContribution params μ ν source target
          px py probeEnergy broadening := by
  unfold projectorBastinTraceIntegrandFor bastinOperatorKernelFromPropagators
    projectorResolvent
  simpa only [bastinBandPairContribution, currentBandBlockTrace,
    scalarSpectralDifferenceCoefficient] using
    (finiteProjectorBastinTrace_eq_band_sum
      (P := fun band : Band => bandProjectorOperator params band px py)
      (bandProjectorOperator_completeOrthogonalIdempotents params px py hE).toOrthogonalIdempotents
      (fun band : Band =>
        scalarResolventCoefficient
          (retardedSpectralParameter probeEnergy broadening)
          (bandEnergy params band px py))
      (fun band : Band =>
        scalarResolventCoefficient
          (advancedSpectralParameter probeEnergy broadening)
          (bandEnergy params band px py))
      (currentBoundedOperator params μ px py)
      (currentBoundedOperator params ν px py))

/-- The existing x-y projector Bastin trace is the ordered band-pair sum. -/
theorem projectorBastinTraceIntegrand_eq_band_sum
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    projectorBastinTraceIntegrand params px py probeEnergy broadening =
      ∑ source : Band, ∑ target : Band,
        bastinBandPairContribution params 0 1 source target
          px py probeEnergy broadening := by
  change projectorBastinTraceIntegrandFor params 0 1 px py probeEnergy broadening = _
  exact projectorBastinTraceIntegrandFor_eq_band_sum
    params 0 1 px py probeEnergy broadening hE

/-- Exact finite-broadening diagonal/interband split of the projector trace. -/
theorem projectorBastinTraceIntegrand_eq_diagonal_add_interband
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    projectorBastinTraceIntegrand params px py probeEnergy broadening =
      diagonalBastinTraceContribution params px py probeEnergy broadening +
        interbandBastinTraceContribution params px py probeEnergy broadening := by
  rw [projectorBastinTraceIntegrand_eq_band_sum params px py probeEnergy broadening hE]
  simp only [sum_band, diagonalBastinTraceContribution, interbandBastinTraceContribution,
    oppositeBand_lower, oppositeBand_upper]
  ring

/-- The canonical regularized Bastin trace agrees with the direction-indexed
projector trace away from spectral degeneracy and at nonzero broadening. -/
theorem regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrandFor
    (params : Parameters) (μ ν : Fin 2) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : broadening ≠ 0) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator params px py)
        (currentBoundedOperator params μ px py)
        (currentBoundedOperator params ν px py)
        probeEnergy broadening =
      projectorBastinTraceIntegrandFor params μ ν px py probeEnergy broadening := by
  simpa only [projectorBastinTraceIntegrandFor, bastinOperatorKernelFromPropagators,
    projectorResolvent] using
    (QuantumTheory.Transport.regularizedBastinTraceIntegrand_eq_projectorSum
      (hamiltonianOperator params px py) (hamiltonianOperator_isSelfAdjoint params px py)
      (fun band : Band => bandProjectorOperator params band px py)
      (fun band : Band => bandEnergy params band px py)
      (bandProjectorOperator_completeOrthogonalIdempotents params px py hE).complete
      (fun band : Band => hamiltonianOperator_mul_bandProjectorOperator params band px py hE)
      (currentBoundedOperator params μ px py) (currentBoundedOperator params ν px py)
      probeEnergy broadening hbroadening)

/-- Direction-indexed canonical Bastin trace equals the ordered band-pair sum. -/
theorem regularizedBastinTraceIntegrand_eq_band_sum
    (params : Parameters) (μ ν : Fin 2) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : broadening ≠ 0) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator params px py)
        (currentBoundedOperator params μ px py)
        (currentBoundedOperator params ν px py)
        probeEnergy broadening =
      ∑ source : Band, ∑ target : Band,
        bastinBandPairContribution params μ ν source target
          px py probeEnergy broadening := by
  rw [regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrandFor
    params μ ν px py probeEnergy broadening hE hbroadening]
  exact projectorBastinTraceIntegrandFor_eq_band_sum
    params μ ν px py probeEnergy broadening hE

/-- For a diagonal source/target band, the Bastin pair is symmetric in
its two current directions at every energy and broadening. This is a
finite-dimensional trace identity, not a clean-limit argument. -/
theorem bastinBandPairContribution_diagonal_swap
    (params : Parameters) (μ ν : Fin 2) (band : Band)
    (px py probeEnergy broadening : ℝ) :
    bastinBandPairContribution params μ ν band band
        px py probeEnergy broadening =
      bastinBandPairContribution params ν μ band band
        px py probeEnergy broadening := by
  unfold bastinBandPairContribution
  dsimp
  rw [currentBandBlockTrace_swap params μ ν band band px py]

/-- Diagonal Bastin band pairs cancel identically in the current-antisymmetric
Hall kernel, even at finite broadening. No energy-integrability assumption is used. -/
theorem antisymmetricBastinBandPairSum_eq_interband
    (params : Parameters) (μ ν : Fin 2)
    (px py probeEnergy broadening : ℝ) :
    (∑ source : Band, ∑ target : Band,
        bastinBandPairContribution params μ ν source target
          px py probeEnergy broadening) -
      (∑ source : Band, ∑ target : Band,
        bastinBandPairContribution params ν μ source target
          px py probeEnergy broadening) =
    (∑ band : Band,
        bastinBandPairContribution params μ ν band (oppositeBand band)
          px py probeEnergy broadening) -
      (∑ band : Band,
        bastinBandPairContribution params ν μ band (oppositeBand band)
          px py probeEnergy broadening) := by
  simp only [sum_band, oppositeBand_lower, oppositeBand_upper]
  rw [bastinBandPairContribution_diagonal_swap params μ ν .lower
      px py probeEnergy broadening,
    bastinBandPairContribution_diagonal_swap params μ ν .upper
      px py probeEnergy broadening]
  ring

/-- The canonical regularized x-y Bastin trace has its original exact
diagonal plus interband decomposition at nonzero broadening. -/
theorem regularizedBastinTraceIntegrand_eq_diagonal_add_interband
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : broadening ≠ 0) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator params px py)
        (currentBoundedOperator params 0 px py)
        (currentBoundedOperator params 1 px py)
        probeEnergy broadening =
      diagonalBastinTraceContribution params px py probeEnergy broadening +
        interbandBastinTraceContribution params px py probeEnergy broadening := by
  rw [regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    params px py probeEnergy broadening hE hbroadening]
  exact projectorBastinTraceIntegrand_eq_diagonal_add_interband
    params px py probeEnergy broadening hE

end

end QuantumTheory.Models.RashbaExchange
