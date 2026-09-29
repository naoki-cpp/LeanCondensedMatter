import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Berry

set_option linter.style.header false

/-!
# Rashba-exchange Bastin band-block decomposition

The projector-expanded finite-broadening Bastin trace is decomposed into the four ordered two-band
pairs.  No diagonal term is discarded, and no zero-broadening or momentum integration is performed
in this module.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open ContinuousLinearMap
open QuantumTheory.Transport

/-- Natural ordered trace `Tr(j_μ P_source j_ν P_target)` produced by the Bastin kernel. -/
noncomputable def bastinBandBlockTrace
    (params : Parameters) (μ ν : Fin 2) (source target : Band) (px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (currentBoundedOperator params μ px py *
      bandProjectorOperator params source px py *
      currentBoundedOperator params ν px py *
      bandProjectorOperator params target px py)

/-- Cyclicity identifies the direct Bastin block with the projector-first current block. -/
theorem bastinBandBlockTrace_eq_currentBandBlockTrace
    (params : Parameters) (μ ν : Fin 2) (source target : Band) (px py : ℝ) :
    bastinBandBlockTrace params μ ν source target px py =
      currentBandBlockTrace params μ ν source target px py := by
  unfold bastinBandBlockTrace currentBandBlockTrace
  calc
    finiteDimensionalOperatorTrace
        (currentBoundedOperator params μ px py *
          bandProjectorOperator params source px py *
          currentBoundedOperator params ν px py *
          bandProjectorOperator params target px py) =
      finiteDimensionalOperatorTrace
        ((currentBoundedOperator params μ px py *
          bandProjectorOperator params source px py *
          currentBoundedOperator params ν px py) *
          bandProjectorOperator params target px py) := by rfl
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator params target px py *
          (currentBoundedOperator params μ px py *
            bandProjectorOperator params source px py *
            currentBoundedOperator params ν px py)) :=
      finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator params target px py *
          currentBoundedOperator params μ px py *
          bandProjectorOperator params source px py *
          currentBoundedOperator params ν px py) := by
      simp only [mul_assoc]

/-- Reversing the current order exchanges source and target labels. -/
theorem bastinBandBlockTrace_swap
    (params : Parameters) (μ ν : Fin 2) (source target : Band) (px py : ℝ) :
    bastinBandBlockTrace params ν μ source target px py =
      bastinBandBlockTrace params μ ν target source px py := by
  unfold bastinBandBlockTrace
  calc
    finiteDimensionalOperatorTrace
        (currentBoundedOperator params ν px py *
          bandProjectorOperator params source px py *
          currentBoundedOperator params μ px py *
          bandProjectorOperator params target px py) =
      finiteDimensionalOperatorTrace
        ((currentBoundedOperator params ν px py *
          bandProjectorOperator params source px py) *
          (currentBoundedOperator params μ px py *
            bandProjectorOperator params target px py)) := by
      simp only [mul_assoc]
    _ = finiteDimensionalOperatorTrace
        ((currentBoundedOperator params μ px py *
          bandProjectorOperator params target px py) *
          (currentBoundedOperator params ν px py *
            bandProjectorOperator params source px py)) :=
      finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace
        (currentBoundedOperator params μ px py *
          bandProjectorOperator params target px py *
          currentBoundedOperator params ν px py *
          bandProjectorOperator params source px py) := by
      simp only [mul_assoc]

/-- Retarded-minus-advanced scalar resolvent coefficient of one band. -/
noncomputable def spectralDifferenceCoefficient
    (params : Parameters) (band : Band) (px py probeEnergy broadening : ℝ) : ℂ :=
  projectorResolventCoefficient
      (retardedSpectralParameter probeEnergy broadening) params band px py -
    projectorResolventCoefficient
      (advancedSpectralParameter probeEnergy broadening) params band px py

/-- Contribution of one ordered band pair to the projector-expanded Bastin trace. -/
noncomputable def bastinBandPairContribution
    (params : Parameters) (μ ν : Fin 2) (source target : Band)
    (px py probeEnergy broadening : ℝ) : ℂ :=
  let r := projectorResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening) params source px py
  let a := projectorResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening) params source px py
  let d := spectralDifferenceCoefficient params target px py probeEnergy broadening
  r ^ 2 * d * bastinBandBlockTrace params μ ν source target px py -
    a ^ 2 * d * bastinBandBlockTrace params ν μ source target px py

/-- Diagonal/intraband part of the finite-broadening Hall trace. -/
noncomputable def diagonalBastinTraceContribution
    (params : Parameters) (px py probeEnergy broadening : ℝ) : ℂ :=
  ∑ band : Band,
    bastinBandPairContribution params 0 1 band band
      px py probeEnergy broadening

/-- Interband part of the finite-broadening Hall trace. -/
noncomputable def interbandBastinTraceContribution
    (params : Parameters) (px py probeEnergy broadening : ℝ) : ℂ :=
  ∑ band : Band,
    bastinBandPairContribution params 0 1 band (oppositeBand band)
      px py probeEnergy broadening

/-- The projector Bastin trace is the sum over all ordered band pairs. -/
theorem projectorBastinTraceIntegrand_eq_band_sum
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    projectorBastinTraceIntegrand params px py probeEnergy broadening =
      ∑ source : Band, ∑ target : Band,
        bastinBandPairContribution params 0 1 source target
          px py probeEnergy broadening := by
  unfold projectorBastinTraceIntegrand
  dsimp only [projectorBastinOperatorIntegrand]
  rw [projectorResolvent_sq
    (retardedSpectralParameter probeEnergy broadening) params px py hE]
  rw [projectorResolvent_sq
    (advancedSpectralParameter probeEnergy broadening) params px py hE]
  simp only [projectorResolvent, sum_band]
  unfold bastinBandPairContribution spectralDifferenceCoefficient bastinBandBlockTrace
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc]
  simp only [map_add, map_sub, map_smul]
  ring_nf

/-- Exact finite-broadening split into diagonal and interband sectors. -/
theorem projectorBastinTraceIntegrand_eq_diagonal_add_interband
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    projectorBastinTraceIntegrand params px py probeEnergy broadening =
      diagonalBastinTraceContribution params px py probeEnergy broadening +
        interbandBastinTraceContribution params px py probeEnergy broadening := by
  rw [projectorBastinTraceIntegrand_eq_band_sum
    params px py probeEnergy broadening hE]
  simp only [sum_band, diagonalBastinTraceContribution,
    interbandBastinTraceContribution, oppositeBand_lower, oppositeBand_upper]
  ring

/-- The repository's generic regularized Bastin trace has the same diagonal/interband split. -/
theorem regularizedBastinTraceIntegrand_eq_diagonal_add_interband
    (params : Parameters) (px py probeEnergy broadening : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hbroadening : 0 < broadening) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator params px py)
        (currentBoundedOperator params 0 px py)
        (currentBoundedOperator params 1 px py)
        probeEnergy broadening =
      diagonalBastinTraceContribution params px py probeEnergy broadening +
        interbandBastinTraceContribution params px py probeEnergy broadening := by
  rw [regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    params px py probeEnergy broadening hE (ne_of_gt hbroadening)]
  exact projectorBastinTraceIntegrand_eq_diagonal_add_interband
    params px py probeEnergy broadening hE

end

end QuantumTheory.Transport.Models.RashbaExchange
