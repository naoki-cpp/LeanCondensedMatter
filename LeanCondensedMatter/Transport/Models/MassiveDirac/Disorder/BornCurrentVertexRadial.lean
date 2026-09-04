import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.PauliRung
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Born-dressed radial retarded-advanced current rung

This Phase 5 bridge feeds the scalar and `σ_z` Born damping channels from `BornPropagator` into the
repository-oriented Green-product part of the current rung

```text
Gᴿ(p,θ) σₓ Gᴬ(p,θ).
```

The full polar-angle integral is specialized from the shared massive-Dirac polar Pauli rung algebra
and closes in the `σₓ`/`σᵧ` span. Its common retarded-advanced denominator product is reduced to a
manifestly real sum of squares, leaving one-dimensional radial integrands ready for the next
Lorentzian/arctangent evaluation.

The operator order is intentionally `Gᴿ σₓ Gᴬ`, matching `Transport.Disorder.Ladder`. Reversing the
retarded/advanced order reverses the orientation-sensitive `σᵧ` coefficient.

There are two normalization levels in this file and they are kept distinct:

* `...RadialXIntegrand` / `...RadialYIntegrand` contain the angular-integrated Green product and the
  polar Jacobian `p dp` only;
* `...CurrentRungRadialXIntegrand` / `...CurrentRungRadialYIntegrand` additionally attach the
  external scalar-disorder line and the physical momentum measure
  `disorderStrength * momentumMeasurePrefactor hbar`.

The angular coefficients already contain the full `2π` polar-angle factor. Therefore the full
current-rung normalization must use `momentumMeasurePrefactor hbar` directly, not
`continuumBornAngularMeasurePrefactor hbar`, which would count that `2π` a second time.

No radial integral, weak-disorder limit, ladder resummation, transport-lifetime identification,
Ward claim, or conductivity theorem is introduced here.
-/

namespace AnomalousHall.MassiveDirac

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
  have hmatrix :
      continuumBornPauliGreenScalarCoefficient side v m
            (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar •
          (1 : Matrix2) +
        continuumBornPauliGreenXCoefficient side v m
            (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar • sigmaX +
        continuumBornPauliGreenYCoefficient side v m
            (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar • sigmaY +
        continuumBornPauliGreenZCoefficient side v m
            (p * Real.cos θ) (p * Real.sin θ) probeEnergy disorderStrength hbar • sigmaZ =
      polarPauliMatrix
        (continuumBornPauliGreenScalarCoefficient
          side v m p 0 probeEnergy disorderStrength hbar)
        (continuumBornPauliGreenXCoefficient
          side v m p 0 probeEnergy disorderStrength hbar)
        (continuumBornPauliGreenZCoefficient
          side v m p 0 probeEnergy disorderStrength hbar) θ := by
    unfold polarPauliMatrix
    unfold continuumBornPauliGreenScalarCoefficient continuumBornPauliGreenXCoefficient
      continuumBornPauliGreenYCoefficient continuumBornPauliGreenZCoefficient
      continuumBornPauliGreenDenominator
    rw [hradial]
    push_cast
    ring_nf
  simpa [continuumBornPauliGreenOperator, polarPauliOperator] using
    congrArg matrixOperator hmatrix

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

/-- Real radial center of the Born retarded/advanced denominator pair. -/
def continuumBornRADenominatorCenter
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  (1 - continuumBornDampingScale v disorderStrength hbar ^ 2) *
      (probeEnergy ^ 2 - m ^ 2) -
    v ^ 2 * p ^ 2

/-- Signed width parameter multiplying `i` in the retarded denominator. -/
def continuumBornRADenominatorWidth
    (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  2 * continuumBornDampingScale v disorderStrength hbar *
    (probeEnergy ^ 2 + m ^ 2)

/-- Manifestly real retarded-advanced denominator product. -/
def continuumBornRADenominatorProduct
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRADenominatorCenter v m p probeEnergy disorderStrength hbar ^ 2 +
    continuumBornRADenominatorWidth v m probeEnergy disorderStrength hbar ^ 2

/-- The real retarded-advanced denominator product is nonnegative. -/
theorem continuumBornRADenominatorProduct_nonneg
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    0 ≤ continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar := by
  unfold continuumBornRADenominatorProduct
  positivity

/-- The radial retarded/advanced denominator product is the real sum of squares `A(p)² + B²`. -/
theorem continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornPauliGreenDenominator
        .retarded v m p 0 probeEnergy disorderStrength hbar *
      continuumBornPauliGreenDenominator
        .advanced v m p 0 probeEnergy disorderStrength hbar =
      (continuumBornRADenominatorProduct
        v m p probeEnergy disorderStrength hbar : ℂ) := by
  rw [continuumBornPauliGreenDenominator_eq_closedForm .retarded,
    continuumBornPauliGreenDenominator_eq_closedForm .advanced]
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  unfold continuumBornRADenominatorProduct continuumBornRADenominatorCenter
    continuumBornRADenominatorWidth
  simp only [SpectralSide.sign_retarded, SpectralSide.sign_advanced]
  push_cast
  ring_nf
  simp [hI]
  ring

/-- Closed Born `σₓ` angular coefficient before replacing the inverse denominator factors by their
real product. -/
theorem continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_inverseFactors
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
theorem continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_inverseFactors
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

/-- Closed radial `σₓ` coefficient with the common real denominator product. -/
theorem continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
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

/-- Closed radial `σᵧ` coefficient with the common real denominator product. The positive sign is
specific to the repository orientation `Gᴿ σₓ Gᴬ`; `Gᴬ σₓ Gᴿ` has the opposite sign. -/
theorem continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
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

/-- Closed real-denominator form of the radial `σₓ` Green-product integrand. -/
theorem continuumBornRetardedAdvancedPauliXRadialXIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialXIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((2 * Real.pi * p *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXRadialXIntegrand,
    continuumBornRetardedAdvancedPauliXAngularXCoefficient_eq_closed]
  push_cast
  ring

/-- Closed real-denominator form of the radial `σᵧ` Green-product integrand. -/
theorem continuumBornRetardedAdvancedPauliXRadialYIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialYIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((8 * Real.pi * p * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXRadialYIntegrand,
    continuumBornRetardedAdvancedPauliXAngularYCoefficient_eq_closed]
  push_cast
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

/-- Closed real-denominator form of the full radial `σₓ` current-rung integrand. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          2 * Real.pi * p *
          (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
          (probeEnergy ^ 2 - m ^ 2) : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialXIntegrand,
    continuumBornRetardedAdvancedPauliXRadialXIntegrand_eq_closed]
  push_cast
  ring

/-- Closed real-denominator form of the full radial `σᵧ` current-rung integrand. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand_eq_closed
    (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand
        v m p probeEnergy disorderStrength hbar =
      (((continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar *
          8 * Real.pi * p * continuumBornDampingScale v disorderStrength hbar *
          probeEnergy * m : ℝ) : ℂ)) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialYIntegrand,
    continuumBornRetardedAdvancedPauliXRadialYIntegrand_eq_closed]
  push_cast
  ring

end

end AnomalousHall.MassiveDirac
