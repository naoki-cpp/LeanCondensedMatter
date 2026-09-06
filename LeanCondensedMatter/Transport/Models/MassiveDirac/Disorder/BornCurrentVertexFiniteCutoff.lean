import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-cutoff Born retarded-advanced current rung

This module owns the Born-dressed current rung from the Cartesian propagator through angular and
radial reduction to the finite-cutoff integral. The full polar-angle `Gᴿ σₓ Gᴬ` product is reduced
with the shared massive-Dirac Pauli rung algebra, reuses the propagator-owned retarded-advanced
denominator pair, and integrates the resulting one-dimensional kernels over radial momentum.

The operator order is intentionally `Gᴿ σₓ Gᴬ`, matching `Transport.Disorder.Ladder`; reversing the
retarded/advanced order reverses the orientation-sensitive `σᵧ` coefficient. The angular
coefficients already contain the full `2π` factor, while the external scalar-disorder line and
physical momentum measure remain explicit through `continuumBornRetardedAdvancedCurrentRungPrefactor`.

Closed forms are exposed direction-independently through the in-plane coefficient matrix
`[[X,-Y],[Y,X]]`; coordinate-specific consumers specialize its indices.

No weak-disorder limit, infinite-cutoff limit, ladder resummation, transport-lifetime
identification, Ward claim, or conductivity theorem is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Proof-local bounded-operator realization of the Cartesian Born-dressed Pauli coefficients. -/
private noncomputable def continuumBornPauliGreenOperator
    (side : SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator
    (continuumBornPauliGreenScalarCoefficient
        side v m px py probeEnergy disorderStrength hbar • (1 : Matrix2) +
      continuumBornPauliGreenXCoefficient
        side v m px py probeEnergy disorderStrength hbar • sigmaX +
      continuumBornPauliGreenYCoefficient
        side v m px py probeEnergy disorderStrength hbar • sigmaY +
      continuumBornPauliGreenZCoefficient
        side v m px py probeEnergy disorderStrength hbar • sigmaZ)

/-- The Cartesian Born-dressed propagator reduces exactly to the shared polar Pauli form. -/
private theorem continuumBornPauliGreenOperator_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenOperator side v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
      polarPauliOperator
        (continuumBornPauliGreenScalarCoefficient
          side v m p 0 probeEnergy disorderStrength hbar)
        (continuumBornPauliGreenXCoefficient
          side v m p 0 probeEnergy disorderStrength hbar)
        (continuumBornPauliGreenZCoefficient
          side v m p 0 probeEnergy disorderStrength hbar) θ := by
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
      continuumBornPauliGreenDenominator side v m
          (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar =
        continuumBornPauliGreenDenominator
          side v m p 0 probeEnergy disorderStrength hbar := by
    unfold continuumBornPauliGreenDenominator
    rw [hradial]
  simpa [continuumBornPauliGreenOperator,
    continuumBornPauliGreenScalarCoefficient,
    continuumBornPauliGreenXCoefficient,
    continuumBornPauliGreenYCoefficient,
    continuumBornPauliGreenZCoefficient, hden] using
    (commonDenominatorPauliOperator_polar_eq
      (continuumBornPauliGreenDenominator
        side v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornEffectiveEnergy side v probeEnergy disorderStrength hbar)
      (continuumBornEffectiveMass side v m disorderStrength hbar)
      v p θ)

/-- `σₓ` coefficient after the full polar-angle integral of the Born-dressed `Gᴿ σₓ Gᴬ` rung. -/
def continuumBornRetardedAdvancedPauliXAngularXCoefficient
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  pauliRungAngularXCoefficient
    (continuumBornPauliGreenScalarCoefficient
      .retarded v m p 0 probeEnergy disorderStrength hbar)
    (continuumBornPauliGreenScalarCoefficient
      .advanced v m p 0 probeEnergy disorderStrength hbar)
    (continuumBornPauliGreenZCoefficient
      .retarded v m p 0 probeEnergy disorderStrength hbar)
    (continuumBornPauliGreenZCoefficient
      .advanced v m p 0 probeEnergy disorderStrength hbar)

/-- Orientation-sensitive `σᵧ` coefficient after the full polar-angle integral of the Born-dressed
`Gᴿ σₓ Gᴬ` rung. The sign flips for `Gᴬ σₓ Gᴿ`. -/
def continuumBornRetardedAdvancedPauliXAngularYCoefficient
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  pauliRungAngularYCoefficient
    (continuumBornPauliGreenScalarCoefficient
      .retarded v m p 0 probeEnergy disorderStrength hbar)
    (continuumBornPauliGreenScalarCoefficient
      .advanced v m p 0 probeEnergy disorderStrength hbar)
    (continuumBornPauliGreenZCoefficient
      .retarded v m p 0 probeEnergy disorderStrength hbar)
    (continuumBornPauliGreenZCoefficient
      .advanced v m p 0 probeEnergy disorderStrength hbar)

/-- Full polar-angle Born-dressed Green-product rung at fixed radial momentum, defined from the
Cartesian Born propagator before reducing to the shared polar form. -/
noncomputable def continuumBornAngularRetardedAdvancedPauliXIntegral
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    continuumBornPauliGreenOperator .retarded v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar *
      matrixOperator sigmaX *
      continuumBornPauliGreenOperator .advanced v m
        (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar

/-- The full Born-dressed Green-product `x`-current rung closes exactly in the in-plane Pauli span. -/
theorem continuumBornAngularRetardedAdvancedPauliXIntegral_eq
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy disorderStrength hbar =
      continuumBornRetardedAdvancedPauliXAngularXCoefficient
          v m p probeEnergy disorderStrength hbar • matrixOperator sigmaX +
        continuumBornRetardedAdvancedPauliXAngularYCoefficient
          v m p probeEnergy disorderStrength hbar • matrixOperator sigmaY := by
  let aR := continuumBornPauliGreenScalarCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let aA := continuumBornPauliGreenScalarCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let bR := continuumBornPauliGreenXCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let bA := continuumBornPauliGreenXCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let dR := continuumBornPauliGreenZCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let dA := continuumBornPauliGreenZCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  unfold continuumBornAngularRetardedAdvancedPauliXIntegral
  have hpolar :
      (fun θ : ℝ =>
        continuumBornPauliGreenOperator .retarded v m
            (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar *
          matrixOperator sigmaX *
          continuumBornPauliGreenOperator .advanced v m
            (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar) =
        fun θ : ℝ =>
          polarPauliOperator aR bR dR θ *
            matrixOperator ((1 : ℂ) • sigmaX + (0 : ℂ) • sigmaY) *
            polarPauliOperator aA bA dA θ := by
    funext θ
    rw [continuumBornPauliGreenOperator_polar_eq,
      continuumBornPauliGreenOperator_polar_eq]
    simp [aR, aA, bR, bA, dR, dA]
  rw [hpolar]
  simpa [continuumBornRetardedAdvancedPauliXAngularXCoefficient,
    continuumBornRetardedAdvancedPauliXAngularYCoefficient,
    aR, aA, bR, bA, dR, dA] using
    (integral_polarPauliOperator_inPlane_eq aR aA bR bA dR dA (1 : ℂ) 0)

/-- Closed Born `σₓ` angular coefficient before replacing the inverse denominator factors by their
real product. -/
private theorem continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_inverseFactors
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularXCoefficient
        v m p probeEnergy disorderStrength hbar =
      (((2 * Real.pi *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
        (continuumBornPauliGreenDenominator
          .retarded v m p 0 probeEnergy disorderStrength hbar)⁻¹ *
        (continuumBornPauliGreenDenominator
          .advanced v m p 0 probeEnergy disorderStrength hbar)⁻¹ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  unfold continuumBornRetardedAdvancedPauliXAngularXCoefficient
    pauliRungAngularXCoefficient
  unfold continuumBornPauliGreenScalarCoefficient continuumBornPauliGreenZCoefficient
  simp [continuumBornEffectiveEnergy, continuumBornEffectiveMass]
  ring_nf
  simp [hI]
  ring

/-- Closed Born `σᵧ` angular coefficient in repository orientation `Gᴿ σₓ Gᴬ`. -/
private theorem continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_inverseFactors
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularYCoefficient
        v m p probeEnergy disorderStrength hbar =
      (((8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m : ℝ) : ℂ)) *
        (continuumBornPauliGreenDenominator
          .retarded v m p 0 probeEnergy disorderStrength hbar)⁻¹ *
        (continuumBornPauliGreenDenominator
          .advanced v m p 0 probeEnergy disorderStrength hbar)⁻¹ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  unfold continuumBornRetardedAdvancedPauliXAngularYCoefficient
    pauliRungAngularYCoefficient
  unfold continuumBornPauliGreenScalarCoefficient continuumBornPauliGreenZCoefficient
  simp [continuumBornEffectiveEnergy, continuumBornEffectiveMass]
  ring_nf
  simp [hI]

/-- Direction-indexed numerator of the closed Born retarded-advanced angular rung. -/
def continuumBornRetardedAdvancedPauliXAngularNumerator
    (i j : Direction2)
    (v m probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  inPlaneRotationCoefficient
    (((2 * Real.pi *
        (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
        (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ))
    (((8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
        probeEnergy * m : ℝ) : ℂ))
    i j

/-- Closed real-denominator form of every direction entry of the Born retarded-advanced angular
rung. Coordinate-specific consumers specialize `i` and `j`. -/
theorem continuumBornRetardedAdvancedPauliXAngularCoefficient_eq_closed
    (i j : Direction2)
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    inPlaneRotationCoefficient
        (continuumBornRetardedAdvancedPauliXAngularXCoefficient
          v m p probeEnergy disorderStrength hbar)
        (continuumBornRetardedAdvancedPauliXAngularYCoefficient
          v m p probeEnergy disorderStrength hbar)
        i j =
      continuumBornRetardedAdvancedPauliXAngularNumerator
          i j v m probeEnergy disorderStrength hbar *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  have hX :
      continuumBornRetardedAdvancedPauliXAngularXCoefficient
          v m p probeEnergy disorderStrength hbar =
        (((2 * Real.pi *
            (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
            (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
          (continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
    rw [continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_inverseFactors]
    rw [← continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq]
    simp [mul_inv_rev]
    ring
  have hY :
      continuumBornRetardedAdvancedPauliXAngularYCoefficient
          v m p probeEnergy disorderStrength hbar =
        (((8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
            probeEnergy * m : ℝ) : ℂ)) *
          (continuumBornRADenominatorProduct
            v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
    rw [continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_inverseFactors]
    rw [← continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq]
    simp [mul_inv_rev]
    ring
  cases i <;> cases j <;>
    simp [inPlaneRotationCoefficient,
      continuumBornRetardedAdvancedPauliXAngularNumerator, hX, hY]

/-- Radial `σₓ` Green-product integrand after angular reduction, including only the polar Jacobian
`p dp`. The external disorder line and physical momentum-measure prefactor are not included. -/
def continuumBornRetardedAdvancedPauliXRadialXIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (p : ℂ) * continuumBornRetardedAdvancedPauliXAngularXCoefficient
    v m p probeEnergy disorderStrength hbar

/-- Radial `σᵧ` Green-product integrand after angular reduction, including only the polar Jacobian
`p dp`. The external disorder line and physical momentum-measure prefactor are not included. -/
def continuumBornRetardedAdvancedPauliXRadialYIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (p : ℂ) * continuumBornRetardedAdvancedPauliXAngularYCoefficient
    v m p probeEnergy disorderStrength hbar

/-- Closed real-denominator form of every direction entry of the radial Green-product integrand. -/
theorem continuumBornRetardedAdvancedPauliXRadialIntegrand_eq_closed
    (i j : Direction2)
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    inPlaneRotationCoefficient
        (continuumBornRetardedAdvancedPauliXRadialXIntegrand
          v m p probeEnergy disorderStrength hbar)
        (continuumBornRetardedAdvancedPauliXRadialYIntegrand
          v m p probeEnergy disorderStrength hbar)
        i j =
      (p : ℂ) *
        continuumBornRetardedAdvancedPauliXAngularNumerator
          i j v m probeEnergy disorderStrength hbar *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  have h := continuumBornRetardedAdvancedPauliXAngularCoefficient_eq_closed
    i j v m p probeEnergy disorderStrength hbar
  cases i <;> cases j <;>
    simp [inPlaneRotationCoefficient,
      continuumBornRetardedAdvancedPauliXRadialXIntegrand,
      continuumBornRetardedAdvancedPauliXRadialYIntegrand] at h ⊢ <;>
    rw [h] <;>
    ring

/-- External scalar-disorder line and physical-momentum measure factor for the continuum RA current
rung. The `2π` angle factor is already contained in the angular coefficients above, so this uses
`momentumMeasurePrefactor hbar` directly rather than `continuumBornAngularMeasurePrefactor hbar`. -/
def continuumBornRetardedAdvancedCurrentRungPrefactor
    (disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * momentumMeasurePrefactor hbar

/-- Full continuum radial `σₓ` current-rung integrand, including the external disorder line and
physical momentum measure but not the radial integral. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
    continuumBornRetardedAdvancedPauliXRadialXIntegrand
      v m p probeEnergy disorderStrength hbar

/-- Full continuum radial `σᵧ` current-rung integrand, including the external disorder line and
physical momentum measure but not the radial integral. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
      v m p probeEnergy disorderStrength hbar

/-- Closed real-denominator form of every direction entry of the normalized radial current rung. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrand_eq_closed
    (i j : Direction2)
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    inPlaneRotationCoefficient
        (continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
          v m p probeEnergy disorderStrength hbar)
        (continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
          v m p probeEnergy disorderStrength hbar)
        i j =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
        (p : ℂ) *
        continuumBornRetardedAdvancedPauliXAngularNumerator
          i j v m probeEnergy disorderStrength hbar *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  have h := continuumBornRetardedAdvancedPauliXRadialIntegrand_eq_closed
    i j v m p probeEnergy disorderStrength hbar
  cases i <;> cases j <;>
    simp [inPlaneRotationCoefficient,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand] at h ⊢ <;>
    rw [h] <;>
    ring

/-- Finite-cutoff radial `σₓ` Green-product coefficient after the proved Born angular reduction. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXRadialXIntegrand
      v m p probeEnergy disorderStrength hbar

/-- Finite-cutoff radial orientation-sensitive `σᵧ` Green-product coefficient after the proved Born
angular reduction. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
    (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
      v m p probeEnergy disorderStrength hbar

/-- The orientation-sensitive radial `σᵧ` Green-product kernel vanishes in the massless model. -/
@[simp] theorem continuumBornRetardedAdvancedPauliXRadialYIntegrand_massless
    (v p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
      v 0 p probeEnergy disorderStrength hbar = 0 := by
  simpa [inPlaneRotationCoefficient,
    continuumBornRetardedAdvancedPauliXAngularNumerator] using
    (continuumBornRetardedAdvancedPauliXRadialIntegrand_eq_closed
      .y .x v 0 p probeEnergy disorderStrength hbar)

/-- The finite-cutoff orientation-sensitive `σᵧ` coefficient vanishes in the massless model. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient_massless
    (v probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
      v 0 probeEnergy disorderStrength hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient]

/-- A zero radial cutoff gives a vanishing Born-dressed RA `σₓ` coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient_zero
    (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialXCoefficient]

/-- A zero radial cutoff gives a vanishing Born-dressed RA `σᵧ` coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient_zero
    (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialYCoefficient]

end

end QuantumTheory.Transport.Models.MassiveDirac
