import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.Berry

set_option linter.style.header false

/-!
# Massive-Dirac Bastin band-block decomposition

The exact finite-broadening Bastin trace from `MassiveDiracBastinBerry` is already written with the
gauge-free two-band projector resolvent. The projector/resolvent algebra itself is owned by
`MassiveDirac/Model/OperatorSpectral`; this file starts from that spectral API and expands the Bastin
expression into the four ordered band blocks

```text
(--), (-+), (+-), (++).
```

The diagonal and interband sectors are kept separate. In particular, no finite-broadening
diagonal term is discarded. The two interband traces are exactly the current-current blocks that
were connected to `e²` times the clean Berry curvature in `MassiveDiracBastinBerry`.

This decomposition is pointwise in probe energy and broadening. Occupation integration and the
zero-broadening limit remain downstream steps.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Ordered current band block `Tr(P_target j_μ P_source j_ν)` used by the Berry bridge. -/
noncomputable def currentBandBlockTrace
    (μ ν : Direction2) (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator target v m px py * currentOperator μ e v *
      bandProjectorOperator source v m px py * currentOperator ν e v)

/-- Natural ordered trace `Tr(j_μ P_source j_ν P_target)` produced by the Bastin kernel. -/
noncomputable def bastinBandBlockTrace
    (μ ν : Direction2) (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (currentOperator μ e v * bandProjectorOperator source v m px py *
      currentOperator ν e v * bandProjectorOperator target v m px py)

/-- Cyclicity identifies the direct Bastin block with the corresponding projector-first block. -/
theorem bastinBandBlockTrace_eq_currentBandBlockTrace
    (μ ν : Direction2) (source target : Band) (e v m px py : ℝ) :
    bastinBandBlockTrace μ ν source target e v m px py =
      currentBandBlockTrace μ ν source target e v m px py := by
  unfold bastinBandBlockTrace currentBandBlockTrace
  calc
    finiteDimensionalOperatorTrace
        (currentOperator μ e v * bandProjectorOperator source v m px py *
          currentOperator ν e v * bandProjectorOperator target v m px py) =
      finiteDimensionalOperatorTrace
        ((currentOperator μ e v * bandProjectorOperator source v m px py *
          currentOperator ν e v) * bandProjectorOperator target v m px py) := by rfl
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator target v m px py *
          (currentOperator μ e v * bandProjectorOperator source v m px py *
            currentOperator ν e v)) :=
      finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator target v m px py * currentOperator μ e v *
          bandProjectorOperator source v m px py * currentOperator ν e v) := by
      simp only [mul_assoc]

/-- Reversing the current order exchanges the source and target labels in the projector-first
block. -/
theorem bastinBandBlockTrace_swap_eq_currentBandBlockTrace
    (μ ν : Direction2) (source target : Band) (e v m px py : ℝ) :
    bastinBandBlockTrace ν μ source target e v m px py =
      currentBandBlockTrace μ ν target source e v m px py := by
  unfold bastinBandBlockTrace currentBandBlockTrace
  calc
    finiteDimensionalOperatorTrace
        (currentOperator ν e v * bandProjectorOperator source v m px py *
          currentOperator μ e v * bandProjectorOperator target v m px py) =
      finiteDimensionalOperatorTrace
        (currentOperator ν e v *
          (bandProjectorOperator source v m px py * currentOperator μ e v *
            bandProjectorOperator target v m px py)) := by
      simp only [mul_assoc]
    _ = finiteDimensionalOperatorTrace
        ((bandProjectorOperator source v m px py * currentOperator μ e v *
          bandProjectorOperator target v m px py) * currentOperator ν e v) := by
      symm
      exact finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator source v m px py * currentOperator μ e v *
          bandProjectorOperator target v m px py * currentOperator ν e v) := by rfl

/-- Difference of retarded and advanced scalar resolvent coefficients for one band. -/
noncomputable def spectralDifferenceCoefficient
    (band : Band) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  projectorResolventCoefficient (retardedSpectralParameter probeEnergy broadening)
      band v m px py -
    projectorResolventCoefficient (advancedSpectralParameter probeEnergy broadening)
      band v m px py

/-- Contribution of one ordered pair `(source,target)` to the projector-expanded Bastin trace. -/
noncomputable def bastinBandPairContribution
    (source target : Band) (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  let r := projectorResolventCoefficient
    (retardedSpectralParameter probeEnergy broadening) source v m px py
  let a := projectorResolventCoefficient
    (advancedSpectralParameter probeEnergy broadening) source v m px py
  let d := spectralDifferenceCoefficient target v m px py probeEnergy broadening
  r ^ 2 * d * bastinBandBlockTrace .x .y source target e v m px py -
    a ^ 2 * d * bastinBandBlockTrace .y .x source target e v m px py

/-- Diagonal/intraband part of the finite-broadening projector Bastin trace. -/
noncomputable def diagonalBastinTraceContribution
    (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  bastinBandPairContribution .lower .lower e v m px py probeEnergy broadening +
    bastinBandPairContribution .upper .upper e v m px py probeEnergy broadening

/-- Interband part of the finite-broadening projector Bastin trace. -/
noncomputable def interbandBastinTraceContribution
    (e v m px py probeEnergy broadening : ℝ) : ℂ :=
  bastinBandPairContribution .lower .upper e v m px py probeEnergy broadening +
    bastinBandPairContribution .upper .lower e v m px py probeEnergy broadening

/-- The full projector Bastin trace is the sum over all four ordered band pairs. -/
theorem projectorBastinTraceIntegrand_eq_four_band_blocks
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) :
    projectorBastinTraceIntegrand e v m px py probeEnergy broadening =
      bastinBandPairContribution .lower .lower e v m px py probeEnergy broadening +
      bastinBandPairContribution .lower .upper e v m px py probeEnergy broadening +
      bastinBandPairContribution .upper .lower e v m px py probeEnergy broadening +
      bastinBandPairContribution .upper .upper e v m px py probeEnergy broadening := by
  unfold projectorBastinTraceIntegrand
  dsimp only [projectorBastinOperatorIntegrand]
  rw [projectorResolvent_sq
    (retardedSpectralParameter probeEnergy broadening) v m px py hE]
  rw [projectorResolvent_sq
    (advancedSpectralParameter probeEnergy broadening) v m px py hE]
  rw [projectorResolvent_eq_coefficients
    (retardedSpectralParameter probeEnergy broadening) v m px py]
  rw [projectorResolvent_eq_coefficients
    (advancedSpectralParameter probeEnergy broadening) v m px py]
  unfold bastinBandPairContribution spectralDifferenceCoefficient bastinBandBlockTrace
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_smul_comm, smul_mul_assoc]
  simp only [map_add, map_sub, map_smul]
  ring_nf

/-- Exact finite-broadening separation into diagonal and interband sectors. -/
theorem projectorBastinTraceIntegrand_eq_diagonal_add_interband
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) :
    projectorBastinTraceIntegrand e v m px py probeEnergy broadening =
      diagonalBastinTraceContribution e v m px py probeEnergy broadening +
        interbandBastinTraceContribution e v m px py probeEnergy broadening := by
  rw [projectorBastinTraceIntegrand_eq_four_band_blocks e v m px py probeEnergy broadening hE]
  unfold diagonalBastinTraceContribution interbandBastinTraceContribution
  ring

/-- Combining the generic Bastin bridge with the band decomposition gives the same diagonal plus
interband split directly for the repository's regularized Bastin trace. -/
theorem regularizedBastinTraceIntegrand_eq_diagonal_add_interband
    (e v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    regularizedBastinTraceIntegrand
        (hamiltonianOperator v m px py)
        (currentOperator .x e v) (currentOperator .y e v) probeEnergy broadening =
      diagonalBastinTraceContribution e v m px py probeEnergy broadening +
        interbandBastinTraceContribution e v m px py probeEnergy broadening := by
  rw [regularizedBastinTraceIntegrand_eq_projectorBastinTraceIntegrand
    e v m px py probeEnergy broadening hE (ne_of_gt hbroadening)]
  exact projectorBastinTraceIntegrand_eq_diagonal_add_interband
    e v m px py probeEnergy broadening hE

end

end AnomalousHall.MassiveDirac
