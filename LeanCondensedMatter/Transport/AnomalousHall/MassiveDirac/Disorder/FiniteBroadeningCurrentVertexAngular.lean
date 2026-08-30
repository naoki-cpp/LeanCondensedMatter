import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current-vertex angular reduction

This module begins the finite-external-broadening current-rung reduction using the actual Born-Dyson
propagator from `FiniteBroadeningBornPropagator.lean`.  The first layer proves that rotational
invariance of the Born self-energy leaves the propagator in the polar Pauli form

```text
G_B,s(p,θ) = a_s(p) I + b_s(p) cosθ σₓ + b_s(p) sinθ σᵧ + d_s(p) σ_z.
```

The radial coefficients remain the existing finite-cutoff finite-`η` Born-Dyson coefficients; no
parallel propagator or self-energy API is introduced.  Radial integration, disorder normalization,
ladder resummation, and broadening/disorder limits remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- The finite-`η` Born-Dyson denominator is rotationally invariant in the momentum plane. -/
theorem finiteCutoffContinuumBornDysonDenominator_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDenominator
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hrad :
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 = p ^ 2 := by
    calc
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
          p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = p ^ 2 := by rw [htrig]; ring
  simp [finiteCutoffContinuumBornDysonDenominator, hrad]

/-- The scalar Born-Dyson Pauli coefficient is independent of polar angle. -/
theorem finiteCutoffContinuumBornDysonScalarCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonScalarCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonScalarCoefficient
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonScalarCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]

/-- The `σₓ` Born-Dyson coefficient is the radial in-plane coefficient times `cos θ`. -/
theorem finiteCutoffContinuumBornDysonXCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonXCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      ((Real.cos θ : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonXCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonXCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]
  push_cast
  ring

/-- The `σᵧ` Born-Dyson coefficient is the same radial in-plane coefficient times `sin θ`. -/
theorem finiteCutoffContinuumBornDysonYCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonYCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      ((Real.sin θ : ℝ) : ℂ) *
        finiteCutoffContinuumBornDysonXCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonYCoefficient finiteCutoffContinuumBornDysonXCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]
  push_cast
  ring

/-- The `σ_z` Born-Dyson Pauli coefficient is independent of polar angle. -/
theorem finiteCutoffContinuumBornDysonZCoefficient_polar
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonZCoefficient
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonZCoefficient
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonZCoefficient
  rw [finiteCutoffContinuumBornDysonDenominator_polar]

/-- Exact polar Pauli form of the finite-`η` Born-Dyson Green matrix. -/
theorem finiteCutoffContinuumBornDysonGreenMatrix_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenMatrix
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonScalarCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) +
        (((Real.cos θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) • sigmaX +
        (((Real.sin θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) • sigmaY +
        finiteCutoffContinuumBornDysonZCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax • sigmaZ := by
  unfold finiteCutoffContinuumBornDysonGreenMatrix
  rw [finiteCutoffContinuumBornDysonScalarCoefficient_polar,
    finiteCutoffContinuumBornDysonXCoefficient_polar,
    finiteCutoffContinuumBornDysonYCoefficient_polar,
    finiteCutoffContinuumBornDysonZCoefficient_polar]

/-- Operator form of the exact polar Pauli decomposition. -/
theorem finiteCutoffContinuumBornDysonGreenOperator_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenOperator
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonScalarCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax •
          (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        (((Real.cos θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) •
          matrixOperator sigmaX +
        (((Real.sin θ : ℝ) : ℂ) *
          finiteCutoffContinuumBornDysonXCoefficient
            side v m p 0 probeEnergy broadening disorderStrength hbar pMax) •
          matrixOperator sigmaY +
        finiteCutoffContinuumBornDysonZCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax •
          matrixOperator sigmaZ := by
  unfold finiteCutoffContinuumBornDysonGreenOperator
  rw [finiteCutoffContinuumBornDysonGreenMatrix_polar_eq]
  simp [matrixOperator, map_add, map_smul]

end

end AnomalousHall.MassiveDirac
