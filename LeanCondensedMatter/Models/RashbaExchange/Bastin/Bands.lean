import LeanCondensedMatter.Models.RashbaExchange.Bastin.Berry
import LeanCondensedMatter.Transport.Streda.InterbandPole

set_option linter.style.header false

/-!
# Rashba-exchange finite-broadening Bastin band-pair decomposition

The finite-projector Bastin trace is an exact ordered sum over source and
target bands. The diagonal sector is retained at nonzero broadening; no
clean-limit or momentum-integral interchange is asserted here. The scalar
kinetic-energy shift remains explicit through the Rashba band energies.
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

/-- The projector Bastin Hall trace is the sum over all ordered source/target
band pairs, without dropping its diagonal contributions. -/
theorem projectorBastinTraceIntegrand_eq_band_sum
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    projectorBastinTraceIntegrand params px py probeEnergy broadening =
      ∑ source : Band, ∑ target : Band,
        bastinBandPairContribution params 0 1 source target
          px py probeEnergy broadening := by
  unfold projectorBastinTraceIntegrand
  dsimp only [projectorBastinOperatorIntegrand, bastinOperatorKernelFromPropagators]
  unfold projectorResolvent
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
      (currentBoundedOperator params 0 px py)
      (currentBoundedOperator params 1 px py))

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

/-- The canonical regularized Bastin Hall trace has the same exact diagonal
plus interband decomposition at nonzero broadening. -/
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
