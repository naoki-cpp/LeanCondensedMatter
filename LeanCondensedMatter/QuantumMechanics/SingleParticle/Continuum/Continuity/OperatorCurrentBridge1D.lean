import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.Continuity.CurrentRepresentation1D
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Velocity-operator bridge for the one-dimensional Schwartz current

The generalized transport stack identifies the conventional one-body probability current with the
Schwartz velocity operator

```text
v = -2 i κ D / ℏ.
```

The first-quantized continuum stack independently packages the usual real probability current

```text
j_ψ(x) = (2 κ / ℏ) Im (star (ψ x) * ψ'(x)).
```

This module proves that these are the same current at the wavefunction level: the standard current
is the local real expectation density of `v`,

```text
j_ψ(x) = Re (star (ψ x) * (v ψ)(x)).
```

The charge-current statement follows by real charge scaling.  The bridge is owned by the concrete
single-particle layer and depends only on the shared analysis operator, so it introduces no
dependency from `QuantumMechanics` to `SecondQuantization`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

/-- Real local expectation density `Re (star ψ * χ)` of two complex Schwartz functions. -/
noncomputable def schwartzRealInnerProductDensity1D
    (ψ χ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
      (schwartzRealPart1D ψ) (schwartzRealPart1D χ) +
    SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
      (schwartzImaginaryPart1D ψ) (schwartzImaginaryPart1D χ)

@[simp]
theorem schwartzRealInnerProductDensity1D_apply
    (ψ χ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzRealInnerProductDensity1D ψ χ x = (star (ψ x) * χ x).re := by
  change (ψ x).re * (χ x).re + (ψ x).im * (χ x).im = (star (ψ x) * χ x).re
  simp [Complex.mul_re]

/-- Local real expectation density of the concrete Schwartz velocity operator. -/
noncomputable def schwartzVelocityExpectationCurrent1D
    (ℏ κ : ℝ) (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  schwartzRealInnerProductDensity1D ψ (SchwartzKinetic1D.velocityOperator ℏ κ ψ)

@[simp]
theorem schwartzVelocityExpectationCurrent1D_apply
    (ℏ κ : ℝ) (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzVelocityExpectationCurrent1D ℏ κ ψ x =
      (star (ψ x) * (SchwartzKinetic1D.velocityOperator ℏ κ ψ) x).re :=
  schwartzRealInnerProductDensity1D_apply ψ _ x

private theorem velocityScalar_eq
    (ℏ κ : ℝ) (hℏ : ℏ ≠ 0) :
    (2 : ℂ) * (Complex.I / (ℏ : ℂ)) * (-(κ : ℂ)) =
      ((-(2 * κ / ℏ) : ℝ) : ℂ) * Complex.I := by
  simp [div_eq_mul_inv]
  field_simp [hℏ]

/-- The pointwise Schrödinger probability current is the real local expectation of the velocity
operator. -/
theorem probabilityCurrentValue1D_eq_velocityExpectation
    (ℏ κ : ℝ) (hℏ : ℏ ≠ 0) (ψ ψx : ℂ) :
    probabilityCurrentValue1D ℏ κ ψ ψx =
      (star ψ *
        (((2 : ℂ) * (Complex.I / (ℏ : ℂ)) * (-(κ : ℂ))) * ψx)).re := by
  rw [velocityScalar_eq ℏ κ hℏ]
  rw [probabilityCurrentValue1D_eq_coordinates]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The bundled Schwartz probability current equals the local expectation density of the velocity
operator. -/
theorem schwartzProbabilityCurrent1D_eq_velocityExpectation
    (ℏ κ : ℝ) (hℏ : ℏ ≠ 0) (ψ : SchwartzMap ℝ ℂ) :
    schwartzProbabilityCurrent1D ℏ κ ψ =
      schwartzVelocityExpectationCurrent1D ℏ κ ψ := by
  ext x
  rw [schwartzProbabilityCurrent1D_apply, schwartzVelocityExpectationCurrent1D_apply]
  simp only [SchwartzKinetic1D.velocityOperator, LinearMap.smul_apply]
  exact probabilityCurrentValue1D_eq_velocityExpectation ℏ κ hℏ
    (ψ x) (schwartzSpatialDerivative1D ψ x)

/-- Pointwise charge current is the charge-scaled real local expectation of the velocity operator. -/
theorem chargeCurrentValue1D_eq_velocityExpectation
    (q ℏ κ : ℝ) (hℏ : ℏ ≠ 0) (ψ ψx : ℂ) :
    chargeCurrentValue1D q ℏ κ ψ ψx =
      q * (star ψ *
        (((2 : ℂ) * (Complex.I / (ℏ : ℂ)) * (-(κ : ℂ))) * ψx)).re := by
  rw [chargeCurrentValue1D]
  rw [probabilityCurrentValue1D_eq_velocityExpectation ℏ κ hℏ]

/-- The bundled Schwartz charge current is the charge-scaled local expectation density of the
velocity operator. -/
theorem schwartzChargeCurrent1D_eq_velocityExpectation
    (q ℏ κ : ℝ) (hℏ : ℏ ≠ 0) (ψ : SchwartzMap ℝ ℂ) :
    schwartzChargeCurrent1D q ℏ κ ψ =
      q • schwartzVelocityExpectationCurrent1D ℏ κ ψ := by
  rw [schwartzChargeCurrent1D, schwartzProbabilityCurrent1D_eq_velocityExpectation ℏ κ hℏ ψ]

end
end Continuum
end SingleParticle
end QuantumMechanics
