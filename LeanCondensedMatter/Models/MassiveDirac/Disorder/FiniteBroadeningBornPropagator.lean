import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.SelfEnergy
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialKernel
import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-external-broadening Born-Dyson propagator

The continuum Born self-energy already exists at finite cutoff and finite external broadening as

```text
Σ_s(ε,η;Λ) = Σ₀,s I + Σ_z,s σ_z.
```

This module constructs the finite-broadening massive-Dirac Green candidate from those
coefficients without first taking `η → 0⁺`. For either spectral side,

```text
ε̃_s = z_s(ε,η) - Σ₀,s,
m̃_s = m + Σ_z,s,
D_s(p) = ε̃_s² - m̃_s² - v²(pₓ²+pᵧ²),
G_B,s = D_s⁻¹ (ε̃_s I + v pₓ σₓ + v pᵧ σᵧ + m̃_s σ_z).
```

The sign `m̃_s = m + Σ_z,s` follows from
`G₀⁻¹ - Σ = (z_s - Σ₀) I - v p·σ - (m + Σ_z) σ_z`.

The radial retarded-advanced denominator product is the finite-`η` specialization of the shared
MassiveDirac radial owner. The propagator itself remains exposed in the shared polar Pauli
representation for downstream angular and radial reductions. Its Dyson-shift inverse
identities and spectral-side adjoint relations are owned downstream by
`FiniteBroadeningBornDysonShift`. This is a finite-cutoff Born-Dyson
approximation candidate. It is not identified with the exact disorder average, and no `η → 0⁺`,
weak-disorder, SCBA/Ward, or conductivity-limit statement is made here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Finite-`η` Born-Dyson effective spectral energy `z_s - Σ₀,s`. -/
noncomputable def finiteCutoffContinuumBornEffectiveEnergy
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  spectralParameter side probeEnergy broadening -
    finiteCutoffContinuumBornSelfEnergyCoefficient .scalar
      side v m probeEnergy broadening disorderStrength hbar pMax

/-- Finite-`η` Born-Dyson effective Dirac mass `m + Σ_z,s`. -/
noncomputable def finiteCutoffContinuumBornEffectiveMass
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (m : ℂ) + finiteCutoffContinuumBornSelfEnergyCoefficient .z
    side v m probeEnergy broadening disorderStrength hbar pMax

/-- Quadratic denominator of the finite-`η` Born-Dyson massive-Dirac propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonDenominator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornEffectiveEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
    finiteCutoffContinuumBornEffectiveMass
      side v m probeEnergy broadening disorderStrength hbar pMax ^ 2 -
    ((v ^ 2 * (px ^ 2 + py ^ 2) : ℝ) : ℂ)

/-- Product of the radial retarded and advanced finite-`η` Born-Dyson denominators. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  massiveDiracRetardedAdvancedRadialDenominatorProduct v p
    (finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax)

/-- The shared radial RA product is exactly the product of the radial retarded and advanced
finite-`η` Born-Dyson denominators. -/
theorem finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_eq_mul
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax =
      finiteCutoffContinuumBornDysonDenominator
          .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax *
        finiteCutoffContinuumBornDysonDenominator
          .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    massiveDiracRetardedAdvancedRadialDenominatorProduct
  congr 1 <;>
    unfold massiveDiracRadialDenominator finiteCutoffContinuumBornDysonDenominator <;>
    push_cast <;>
    ring

/-- Scalar Pauli coefficient of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonScalarCoefficient
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
    finiteCutoffContinuumBornEffectiveEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax

/-- Direction-indexed Pauli-vector coefficient of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonPauliCoefficient
    (axis : PauliAxis) (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (finiteCutoffContinuumBornDysonDenominator
      side v m px py probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
    InternalSpace.pauliAxisComponent axis
      (((v * px : ℝ) : ℂ))
      (((v * py : ℝ) : ℂ))
      (finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax)

/-- Matrix form of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonGreenMatrix
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) : Matrix2 :=
  finiteCutoffContinuumBornDysonScalarCoefficient
      side v m px py probeEnergy broadening disorderStrength hbar pMax • (1 : Matrix2) +
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m px py probeEnergy broadening disorderStrength hbar pMax • sigmaX +
    finiteCutoffContinuumBornDysonPauliCoefficient .y
      side v m px py probeEnergy broadening disorderStrength hbar pMax • sigmaY +
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m px py probeEnergy broadening disorderStrength hbar pMax • sigmaZ

/-- Bounded-operator form of the finite-`η` Born-Dyson propagator candidate. -/
noncomputable def finiteCutoffContinuumBornDysonGreenOperator
    (side : SpectralSide)
    (v m px py probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator
    (finiteCutoffContinuumBornDysonGreenMatrix
      side v m px py probeEnergy broadening disorderStrength hbar pMax)

/-- The Cartesian finite-`η` Born-Dyson propagator reduces exactly to the shared polar Pauli form. -/
theorem finiteCutoffContinuumBornDysonGreenOperator_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenOperator
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      polarPauliOperator
        (finiteCutoffContinuumBornDysonScalarCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonPauliCoefficient .x
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonPauliCoefficient .z
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax) θ := by
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hradial :
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 = p ^ 2 + 0 ^ 2 := by
    calc
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
          p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = p ^ 2 := by rw [htrig]; ring
      _ = p ^ 2 + 0 ^ 2 := by ring
  have hden :
      finiteCutoffContinuumBornDysonDenominator
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonDenominator
    rw [hradial]
  simpa [finiteCutoffContinuumBornDysonGreenOperator,
    finiteCutoffContinuumBornDysonGreenMatrix,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient, InternalSpace.pauliAxisComponent, hden] using
    (commonDenominatorPauliOperator_polar_eq
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax)
      v p θ)

/-- At zero disorder strength the finite-`η` Born-Dyson denominator reduces to the clean Pauli Green
denominator. -/
@[simp] theorem finiteCutoffContinuumBornDysonDenominator_zero_disorder
    (side : SpectralSide)
    (v m px py probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonDenominator
        side v m px py probeEnergy broadening 0 hbar pMax =
      pauliGreenDenominator side v m px py probeEnergy broadening := by
  unfold pauliGreenDenominator
  simp [finiteCutoffContinuumBornDysonDenominator,
    finiteCutoffContinuumBornEffectiveEnergy,
    finiteCutoffContinuumBornEffectiveMass,
    pauliGreenDenominatorOfRegulator, spectralParameter, energySq]
  ring

/-- At zero disorder strength the finite-`η` Born-Dyson propagator candidate is exactly the clean
massive-Dirac Pauli Green operator. -/
@[simp] theorem finiteCutoffContinuumBornDysonGreenOperator_zero_disorder
    (side : SpectralSide)
    (v m px py probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenOperator
        side v m px py probeEnergy broadening 0 hbar pMax =
      pauliGreenOperator side v m px py probeEnergy broadening := by
  unfold finiteCutoffContinuumBornDysonGreenOperator
    finiteCutoffContinuumBornDysonGreenMatrix
    finiteCutoffContinuumBornDysonScalarCoefficient
    finiteCutoffContinuumBornDysonPauliCoefficient
    pauliGreenOperator pauliGreenOperatorOfRegulator
    pauliGreenScalarCoefficientOfRegulator pauliGreenPauliCoefficientOfRegulator
    pauliGreenDenominatorOfRegulator
  simp [finiteCutoffContinuumBornEffectiveEnergy,
    finiteCutoffContinuumBornEffectiveMass, spectralParameter,
    pauliGreenDenominator, pauliGreenDenominatorOfRegulator, InternalSpace.pauliAxisComponent,
    matrixOperator, map_add, map_smul]

end

end QuantumTheory.Models.MassiveDirac
