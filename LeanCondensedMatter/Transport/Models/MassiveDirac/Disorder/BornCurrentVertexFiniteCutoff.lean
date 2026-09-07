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
retarded/advanced order reverses the orientation-sensitive `σᵧ` coefficient. The source is fixed to
`σₓ`, while the in-plane output component is represented explicitly by `Direction2`. The angular
coefficients already contain the full `2π` factor, while the external scalar-disorder line and
physical momentum measure remain explicit through `continuumBornRetardedAdvancedCurrentRungPrefactor`.

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
      continuumBornPauliGreenPauliCoefficient .x
        side v m px py probeEnergy disorderStrength hbar • sigmaX +
      continuumBornPauliGreenPauliCoefficient .y
        side v m px py probeEnergy disorderStrength hbar • sigmaY +
      continuumBornPauliGreenPauliCoefficient .z
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
        (continuumBornPauliGreenPauliCoefficient .x
          side v m p 0 probeEnergy disorderStrength hbar)
        (continuumBornPauliGreenPauliCoefficient .z
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
    continuumBornPauliGreenPauliCoefficient, pauliAxisComponent, hden] using
    (commonDenominatorPauliOperator_polar_eq
      (continuumBornPauliGreenDenominator
        side v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornEffectiveEnergy side v probeEnergy disorderStrength hbar)
      (continuumBornEffectiveMass side v m disorderStrength hbar)
      v p θ)

/-- Output-direction coefficient after the full polar-angle integral of the Born-dressed
`Gᴿ σₓ Gᴬ` rung. The `.y` sign is specific to this retarded/advanced ordering. -/
def continuumBornRetardedAdvancedPauliXAngularCoefficient
    (output : Direction2)
    (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  match output with
  | .x => pauliRungAngularXCoefficient
      (continuumBornPauliGreenScalarCoefficient
        .retarded v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornPauliGreenScalarCoefficient
        .advanced v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornPauliGreenPauliCoefficient .z
        .retarded v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornPauliGreenPauliCoefficient .z
        .advanced v m p 0 probeEnergy disorderStrength hbar)
  | .y => pauliRungAngularYCoefficient
      (continuumBornPauliGreenScalarCoefficient
        .retarded v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornPauliGreenScalarCoefficient
        .advanced v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornPauliGreenPauliCoefficient .z
        .retarded v m p 0 probeEnergy disorderStrength hbar)
      (continuumBornPauliGreenPauliCoefficient .z
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
      continuumBornRetardedAdvancedPauliXAngularCoefficient .x
          v m p probeEnergy disorderStrength hbar • matrixOperator sigmaX +
        continuumBornRetardedAdvancedPauliXAngularCoefficient .y
          v m p probeEnergy disorderStrength hbar • matrixOperator sigmaY := by
  let aR := continuumBornPauliGreenScalarCoefficient
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let aA := continuumBornPauliGreenScalarCoefficient
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let bR := continuumBornPauliGreenPauliCoefficient .x
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let bA := continuumBornPauliGreenPauliCoefficient .x
    .advanced v m p 0 probeEnergy disorderStrength hbar
  let dR := continuumBornPauliGreenPauliCoefficient .z
    .retarded v m p 0 probeEnergy disorderStrength hbar
  let dA := continuumBornPauliGreenPauliCoefficient .z
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
  simpa [continuumBornRetardedAdvancedPauliXAngularCoefficient,
    aR, aA, bR, bA, dR, dA] using
    (integral_polarPauliOperator_inPlane_eq aR aA bR bA dR dA (1 : ℂ) 0)

/-- Real numerator multiplying the common retarded-advanced denominator product in the selected
output direction. -/
def continuumBornRetardedAdvancedPauliXAngularNumerator
    (output : Direction2) (v m probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  match output with
  | .x => 2 * Real.pi *
      (1 + continuumBornDampingScale v disorderStrength hbar ^ 2) *
      (probeEnergy ^ 2 - m ^ 2)
  | .y => 8 * Real.pi * continuumBornDampingScale v disorderStrength hbar *
      probeEnergy * m

/-- Closed Born angular coefficient before replacing the inverse denominator factors by their real
product. -/
private theorem continuumBornRetardedAdvancedPauliXAngularCoefficient_eq_inverseFactors
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularCoefficient output
        v m p probeEnergy disorderStrength hbar =
      (continuumBornRetardedAdvancedPauliXAngularNumerator output
          v m probeEnergy disorderStrength hbar : ℂ) *
        (continuumBornPauliGreenDenominator
          .retarded v m p 0 probeEnergy disorderStrength hbar)⁻¹ *
        (continuumBornPauliGreenDenominator
          .advanced v m p 0 probeEnergy disorderStrength hbar)⁻¹ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  cases output
  · unfold continuumBornRetardedAdvancedPauliXAngularCoefficient
      continuumBornRetardedAdvancedPauliXAngularNumerator pauliRungAngularXCoefficient
    unfold continuumBornPauliGreenScalarCoefficient continuumBornPauliGreenPauliCoefficient
    simp [pauliAxisComponent, continuumBornEffectiveEnergy, continuumBornEffectiveMass]
    ring_nf
    simp [hI]
    ring
  · unfold continuumBornRetardedAdvancedPauliXAngularCoefficient
      continuumBornRetardedAdvancedPauliXAngularNumerator pauliRungAngularYCoefficient
    unfold continuumBornPauliGreenScalarCoefficient continuumBornPauliGreenPauliCoefficient
    simp [pauliAxisComponent, continuumBornEffectiveEnergy, continuumBornEffectiveMass]
    ring_nf
    simp [hI]

/-- Closed real-denominator form of either in-plane angular coefficient. -/
theorem continuumBornRetardedAdvancedPauliXAngularCoefficient_eq_closed
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXAngularCoefficient output
        v m p probeEnergy disorderStrength hbar =
      (continuumBornRetardedAdvancedPauliXAngularNumerator output
          v m probeEnergy disorderStrength hbar : ℂ) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXAngularCoefficient_eq_inverseFactors]
  rw [← continuumBornPauliGreenDenominator_retarded_mul_advanced_radial_eq]
  simp [mul_inv_rev]
  ring

/-- Radial Green-product integrand in the selected output direction after angular reduction,
including only the polar Jacobian `p dp`. -/
def continuumBornRetardedAdvancedPauliXRadialIntegrand
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (p : ℂ) * continuumBornRetardedAdvancedPauliXAngularCoefficient output
    v m p probeEnergy disorderStrength hbar

/-- Closed real-denominator form of the direction-indexed radial Green-product integrand. -/
theorem continuumBornRetardedAdvancedPauliXRadialIntegrand_eq_closed
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialIntegrand output
        v m p probeEnergy disorderStrength hbar =
      ((p * continuumBornRetardedAdvancedPauliXAngularNumerator output
          v m probeEnergy disorderStrength hbar : ℝ) : ℂ) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXRadialIntegrand,
    continuumBornRetardedAdvancedPauliXAngularCoefficient_eq_closed]
  push_cast
  ring

/-- External scalar-disorder line and physical-momentum measure factor for the continuum RA current
rung. The `2π` angle factor is already contained in the angular coefficients above, so this uses
`momentumMeasurePrefactor hbar` directly rather than `continuumBornAngularMeasurePrefactor hbar`. -/
def continuumBornRetardedAdvancedCurrentRungPrefactor
    (disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * momentumMeasurePrefactor hbar

/-- Full continuum radial current-rung integrand in the selected output direction, including the
external disorder line and physical momentum measure but not the radial integral. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrand
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) : ℂ :=
  (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
    continuumBornRetardedAdvancedPauliXRadialIntegrand output
      v m p probeEnergy disorderStrength hbar

/-- Closed real-denominator form of the direction-indexed full radial current-rung integrand. -/
theorem continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrand_eq_closed
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrand output
        v m p probeEnergy disorderStrength hbar =
      ((continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar * p *
          continuumBornRetardedAdvancedPauliXAngularNumerator output
            v m probeEnergy disorderStrength hbar : ℝ) : ℂ) *
        (continuumBornRADenominatorProduct
          v m p probeEnergy disorderStrength hbar : ℂ)⁻¹ := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrand,
    continuumBornRetardedAdvancedPauliXRadialIntegrand_eq_closed]
  push_cast
  ring

/-- Real-valued form of the normalized radial current-rung integrand in either output direction. -/
def continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) : ℝ :=
  continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar * p *
    continuumBornRetardedAdvancedPauliXAngularNumerator output
      v m probeEnergy disorderStrength hbar *
    (continuumBornRADenominatorProduct
      v m p probeEnergy disorderStrength hbar)⁻¹

/-- The indexed real current-rung kernel embeds exactly into the complex radial API. -/
theorem coe_continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal
    (output : Direction2) (v m p probeEnergy disorderStrength hbar : ℝ) :
    (continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal output
        v m p probeEnergy disorderStrength hbar : ℂ) =
      continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrand output
        v m p probeEnergy disorderStrength hbar := by
  rw [continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrand_eq_closed]
  unfold continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal
  push_cast
  ring

/-- Finite-cutoff radial Green-product coefficient in the selected in-plane output direction. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient
    (output : Direction2) (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXRadialIntegrand output
      v m p probeEnergy disorderStrength hbar

/-- Finite-cutoff real coefficient of the fully normalized Born RA current rung in the selected
output direction. -/
noncomputable def finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient
    (output : Direction2) (v m probeEnergy disorderStrength hbar pMax : ℝ) : ℝ :=
  ∫ p in (0 : ℝ)..pMax,
    continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal output
      v m p probeEnergy disorderStrength hbar

/-- The real normalized finite-cutoff coefficient is the indexed Green-product coefficient
multiplied by the physical current-rung prefactor. -/
theorem coe_finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_eq_prefactor_mul_greenProduct
    (output : Direction2) (v m probeEnergy disorderStrength hbar pMax : ℝ) :
    (finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient output
        v m probeEnergy disorderStrength hbar pMax : ℂ) =
      (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
        finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient output
          v m probeEnergy disorderStrength hbar pMax := by
  unfold finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient
  rw [← Complex.ofRealLI_apply
    (∫ p in (0 : ℝ)..pMax,
      continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal output
        v m p probeEnergy disorderStrength hbar)]
  rw [← Complex.ofRealLI.intervalIntegral_comp_comm]
  rw [show
      (fun p : ℝ => Complex.ofRealLI
        (continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal output
          v m p probeEnergy disorderStrength hbar)) =
      (fun p : ℝ =>
        (continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar : ℂ) *
          continuumBornRetardedAdvancedPauliXRadialIntegrand output
            v m p probeEnergy disorderStrength hbar) by
    funext p
    rw [Complex.ofRealLI_apply,
      coe_continuumBornRetardedAdvancedPauliXCurrentRungRadialIntegrandReal]
    rfl]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- The orientation-sensitive radial `.y` Green-product kernel vanishes in the massless model. -/
@[simp] theorem continuumBornRetardedAdvancedPauliXRadialIntegrand_y_massless
    (v p probeEnergy disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedPauliXRadialIntegrand .y
      v 0 p probeEnergy disorderStrength hbar = 0 := by
  rw [continuumBornRetardedAdvancedPauliXRadialIntegrand_eq_closed]
  simp [continuumBornRetardedAdvancedPauliXAngularNumerator]

/-- The finite-cutoff orientation-sensitive `.y` coefficient vanishes in the massless model. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient_y_massless
    (v probeEnergy disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient .y
      v 0 probeEnergy disorderStrength hbar pMax = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient]

/-- A zero radial cutoff gives a vanishing Born-dressed RA Green-product coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient_zero
    (output : Direction2) (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient output
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXRadialCoefficient]

/-- A zero radial cutoff gives a vanishing normalized current-rung coefficient. -/
@[simp] theorem finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient_zero
    (output : Direction2) (v m probeEnergy disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient output
      v m probeEnergy disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornRetardedAdvancedPauliXCurrentRungCoefficient]

end

end QuantumTheory.Transport.Models.MassiveDirac
