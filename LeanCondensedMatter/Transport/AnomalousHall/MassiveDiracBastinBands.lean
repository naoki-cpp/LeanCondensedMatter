import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinBerry

set_option linter.style.header false

/-!
# Massive-Dirac Bastin band-block decomposition

The exact finite-broadening Bastin trace from `MassiveDiracBastinBerry` is already written with the
gauge-free two-band projector resolvent. This file expands that expression into the four ordered
band blocks

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

/-- Scalar coefficient of band `band` in the gauge-free projector resolvent at spectral parameter
`z`. -/
noncomputable def projectorResolventCoefficient
    (z : ℂ) (band : Band) (v m px py : ℝ) : ℂ :=
  (z - ((bandEnergy band v m px py : ℝ) : ℂ))⁻¹

/-- Operator projectors remain idempotent after transport from `2 × 2` matrices. -/
theorem bandProjectorOperator_mul_self
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator band v m px py * bandProjectorOperator band v m px py =
      bandProjectorOperator band v m px py := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector band v m px py) * φ (bandProjector band v m px py) =
    φ (bandProjector band v m px py)
  calc
    φ (bandProjector band v m px py) * φ (bandProjector band v m px py) =
        φ (bandProjector band v m px py * bandProjector band v m px py) := by
      symm
      exact map_mul φ _ _
    _ = φ (bandProjector band v m px py) := by
      rw [bandProjector_mul_self band v m px py hE]

/-- Lower then upper operator projectors are orthogonal away from the Dirac degeneracy. -/
theorem bandProjectorOperator_lower_mul_upper
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator .lower v m px py * bandProjectorOperator .upper v m px py = 0 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector .lower v m px py) * φ (bandProjector .upper v m px py) = 0
  calc
    φ (bandProjector .lower v m px py) * φ (bandProjector .upper v m px py) =
        φ (bandProjector .lower v m px py * bandProjector .upper v m px py) := by
      symm
      exact map_mul φ _ _
    _ = 0 := by rw [bandProjector_lower_mul_upper v m px py hE, map_zero]

/-- Upper then lower operator projectors are orthogonal away from the Dirac degeneracy. -/
theorem bandProjectorOperator_upper_mul_lower
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator .upper v m px py * bandProjectorOperator .lower v m px py = 0 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector .upper v m px py) * φ (bandProjector .lower v m px py) = 0
  calc
    φ (bandProjector .upper v m px py) * φ (bandProjector .lower v m px py) =
        φ (bandProjector .upper v m px py * bandProjector .lower v m px py) := by
      symm
      exact map_mul φ _ _
    _ = 0 := by rw [bandProjector_upper_mul_lower v m px py hE, map_zero]

/-- The projector resolvent written using the named scalar band coefficients. -/
theorem projectorResolvent_eq_coefficients
    (z : ℂ) (v m px py : ℝ) :
    projectorResolvent z v m px py =
      projectorResolventCoefficient z .lower v m px py •
          bandProjectorOperator .lower v m px py +
        projectorResolventCoefficient z .upper v m px py •
          bandProjectorOperator .upper v m px py := by
  rfl

/-- Squaring the two-band projector resolvent squares only its scalar spectral coefficients. -/
theorem projectorResolvent_sq
    (z : ℂ) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    projectorResolvent z v m px py ^ 2 =
      projectorResolventCoefficient z .lower v m px py ^ 2 •
          bandProjectorOperator .lower v m px py +
        projectorResolventCoefficient z .upper v m px py ^ 2 •
          bandProjectorOperator .upper v m px py := by
  rw [projectorResolvent_eq_coefficients, pow_two]
  rw [add_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [bandProjectorOperator_mul_self .lower v m px py hE]
  rw [bandProjectorOperator_mul_self .upper v m px py hE]
  rw [bandProjectorOperator_lower_mul_upper v m px py hE]
  rw [bandProjectorOperator_upper_mul_lower v m px py hE]
  simp [pow_two]

/-- Ordered Hall band block `Tr(P_target jₓ P_source jᵧ)` used by the Berry bridge. -/
noncomputable def currentBandBlockTrace
    (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator target v m px py * currentOperator .x e v *
      bandProjectorOperator source v m px py * currentOperator .y e v)

/-- Natural `x-y` ordered trace produced directly by expanding the Bastin kernel. -/
noncomputable def bastinXYBandBlockTrace
    (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (currentOperator .x e v * bandProjectorOperator source v m px py *
      currentOperator .y e v * bandProjectorOperator target v m px py)

/-- Natural `y-x` ordered trace produced directly by the advanced part of the Bastin kernel. -/
noncomputable def bastinYXBandBlockTrace
    (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (currentOperator .y e v * bandProjectorOperator source v m px py *
      currentOperator .x e v * bandProjectorOperator target v m px py)

/-- Cyclicity identifies the direct `x-y` Bastin block with the Berry-bridge block. -/
theorem bastinXYBandBlockTrace_eq_currentBandBlockTrace
    (source target : Band) (e v m px py : ℝ) :
    bastinXYBandBlockTrace source target e v m px py =
      currentBandBlockTrace source target e v m px py := by
  unfold bastinXYBandBlockTrace currentBandBlockTrace
  calc
    finiteDimensionalOperatorTrace
        (currentOperator .x e v * bandProjectorOperator source v m px py *
          currentOperator .y e v * bandProjectorOperator target v m px py) =
      finiteDimensionalOperatorTrace
        ((currentOperator .x e v * bandProjectorOperator source v m px py *
          currentOperator .y e v) * bandProjectorOperator target v m px py) := by rfl
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator target v m px py *
          (currentOperator .x e v * bandProjectorOperator source v m px py *
            currentOperator .y e v)) :=
      finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator target v m px py * currentOperator .x e v *
          bandProjectorOperator source v m px py * currentOperator .y e v) := by
      simp only [mul_assoc]

/-- Cyclicity identifies the direct `y-x` block with the reversed Berry-bridge block. -/
theorem bastinYXBandBlockTrace_eq_reversedCurrentBandBlockTrace
    (source target : Band) (e v m px py : ℝ) :
    bastinYXBandBlockTrace source target e v m px py =
      currentBandBlockTrace target source e v m px py := by
  unfold bastinYXBandBlockTrace currentBandBlockTrace
  calc
    finiteDimensionalOperatorTrace
        (currentOperator .y e v * bandProjectorOperator source v m px py *
          currentOperator .x e v * bandProjectorOperator target v m px py) =
      finiteDimensionalOperatorTrace
        (currentOperator .y e v *
          (bandProjectorOperator source v m px py * currentOperator .x e v *
            bandProjectorOperator target v m px py)) := by
      simp only [mul_assoc]
    _ = finiteDimensionalOperatorTrace
        ((bandProjectorOperator source v m px py * currentOperator .x e v *
          bandProjectorOperator target v m px py) * currentOperator .y e v) := by
      symm
      exact finiteDimensionalOperatorTrace_mul_comm _ _
    _ = finiteDimensionalOperatorTrace
        (bandProjectorOperator source v m px py * currentOperator .x e v *
          bandProjectorOperator target v m px py * currentOperator .y e v) := by rfl

/-- The lower-to-upper ordered block is the lower-band Hall interband trace. -/
theorem currentBandBlockTrace_lower_upper
    (e v m px py : ℝ) :
    currentBandBlockTrace .lower .upper e v m px py =
      interbandCurrentTrace .x .y .lower e v m px py := by
  rfl

/-- The upper-to-lower ordered block is the upper-band Hall interband trace. -/
theorem currentBandBlockTrace_upper_lower
    (e v m px py : ℝ) :
    currentBandBlockTrace .upper .lower e v m px py =
      interbandCurrentTrace .x .y .upper e v m px py := by
  rfl

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
  r ^ 2 * d * bastinXYBandBlockTrace source target e v m px py -
    a ^ 2 * d * bastinYXBandBlockTrace source target e v m px py

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
  unfold bastinBandPairContribution spectralDifferenceCoefficient
    bastinXYBandBlockTrace bastinYXBandBlockTrace
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
    e v m px py probeEnergy broadening hE hbroadening]
  exact projectorBastinTraceIntegrand_eq_diagonal_add_interband
    e v m px py probeEnergy broadening hE

end

end AnomalousHall.MassiveDirac
