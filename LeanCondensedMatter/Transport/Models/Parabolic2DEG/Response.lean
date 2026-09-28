import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Models.Parabolic2DEG.Model
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-cutoff finite-broadening parabolic-2DEG response

This module owns the radial/angular reduction and normalization boundary for the parabolic benchmark.
The finite response keeps `p_max`, `η`, the measure normalization, and the remaining response
normalization explicit. Consumers use `finiteCutoffConductivityTensor` rather than reconstructing
the current product, polar Jacobian, or normalization factors.

The off-diagonal cancellation proved below is a consequence of the isotropic angular harmonics of
this benchmark. It is not a claim about a generic two-dimensional system and does not introduce a
nonzero Hall response.
-/

namespace QuantumTheory.Transport.Models.Parabolic2DEG

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Radial current scale `q p / m_eff` before angular projection. -/
def radialCurrentScale (params : Parameters) (p : ℝ) : ℝ :=
  params.signedCharge * p / params.effectiveMass

/-- Canonical constant/second-harmonic representation of the product of two Cartesian current
components on a circle of radius `p`.

For equal directions the constant piece is one half of `(q p / m_eff)²`; the second-cosine
coefficient distinguishes `xx` from `yy`. For unequal directions the product is purely the mixed
second harmonic. -/
def currentProductAngularCoefficients
    (params : Parameters) (measured source : Fin 2) (p : ℝ) :
    AngularHarmonicCoefficients ℂ :=
  let amplitude : ℂ := (((radialCurrentScale params p) ^ 2 : ℝ) : ℂ)
  if _hEq : measured = source then
    if _hX : measured = 0 then
      { constant := amplitude / 2
        firstCosine := 0
        firstSine := 0
        secondCosine := amplitude / 2
        secondMixed := 0 }
    else
      { constant := amplitude / 2
        firstCosine := 0
        firstSine := 0
        secondCosine := -(amplitude / 2)
        secondMixed := 0 }
  else
    { constant := 0
      firstCosine := 0
      firstSine := 0
      secondCosine := 0
      secondMixed := amplitude }

/-- Full-angle current-product factor owned by the model-level response boundary. -/
def angularIntegratedCurrentProduct
    (params : Parameters) (measured source : Fin 2) (p : ℝ) : ℂ :=
  (2 * Real.pi : ℝ) •
    (currentProductAngularCoefficients params measured source p).constant

/-- The model-level angular reduction is exactly the integral of the canonical harmonic
representation. -/
theorem angularIntegratedCurrentProduct_eq_integral
    (params : Parameters) (measured source : Fin 2) (p : ℝ) :
    angularIntegratedCurrentProduct params measured source p =
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        (currentProductAngularCoefficients params measured source p).eval θ := by
  symm
  simpa [angularIntegratedCurrentProduct] using
    (currentProductAngularCoefficients params measured source p).integral_eval

/-- The retarded-advanced scalar Green weight at radial momentum `p`. -/
def retardedAdvancedWeight (params : Parameters) (p : ℝ) : ℂ :=
  greenScalar .retarded params p 0 * greenScalar .advanced params p 0

/-- The retarded-advanced radial Green weight is continuous for finite nonzero broadening. -/
theorem continuous_retardedAdvancedWeight
    (params : Parameters) (hbroadening : params.broadening ≠ 0) :
    Continuous (retardedAdvancedWeight params) := by
  exact (continuous_greenScalar_radial .retarded params hbroadening).mul
    (continuous_greenScalar_radial .advanced params hbroadening)

/-- Radial finite-broadening response kernel after exact full-angle reduction. The leading `p`
is the polar Jacobian. -/
def finiteBroadeningRadialKernel
    (params : Parameters) (measured source : Fin 2) (p : ℝ) : ℂ :=
  ((p : ℝ) : ℂ) *
    angularIntegratedCurrentProduct params measured source p *
      retardedAdvancedWeight params p

/-- Finite-cutoff, finite-broadening ordered response component. All measure and response
normalizations are attached exactly once at this model boundary. -/
noncomputable def finiteCutoffResponseComponent
    (params : Parameters) (measured source : Fin 2) : ℂ :=
  (((params.responseNormalization * params.momentumMeasureNormalization : ℝ) : ℂ)) *
    ∫ p : ℝ in (0 : ℝ)..params.momentumCutoff,
      finiteBroadeningRadialKernel params measured source p

/-- Common physical transport seam for the finite parabolic benchmark. -/
noncomputable def finiteCutoffConductivityTensor
    (params : Parameters) : ConductivityTensor (Fin 2) where
  component := finiteCutoffResponseComponent params

@[simp]
theorem finiteCutoffConductivityTensor_component
    (params : Parameters) (measured source : Fin 2) :
    (finiteCutoffConductivityTensor params).component measured source =
      finiteCutoffResponseComponent params measured source := rfl

/-- The isotropic current product has no constant angular harmonic for unequal directions. -/
theorem angularIntegratedCurrentProduct_eq_zero_of_ne
    (params : Parameters) (measured source : Fin 2) (hne : measured ≠ source) (p : ℝ) :
    angularIntegratedCurrentProduct params measured source p = 0 := by
  simp [angularIntegratedCurrentProduct, currentProductAngularCoefficients, hne]

/-- Under the explicit off-diagonal hypothesis, the finite isotropic response component vanishes. -/
theorem finiteCutoffResponseComponent_eq_zero_of_ne
    (params : Parameters) (measured source : Fin 2) (hne : measured ≠ source) :
    finiteCutoffResponseComponent params measured source = 0 := by
  unfold finiteCutoffResponseComponent finiteBroadeningRadialKernel
  simp [angularIntegratedCurrentProduct_eq_zero_of_ne params measured source hne]

/-- Under the explicit off-diagonal hypothesis, the Hall projection of the isotropic benchmark
vanishes. -/
theorem finiteCutoffConductivityTensor_hallComponent_eq_zero_of_ne
    (params : Parameters) (i j : Fin 2) (hne : i ≠ j) :
    (finiteCutoffConductivityTensor params).hallComponent i j = 0 := by
  rw [ConductivityTensor.hallComponent]
  simp [finiteCutoffResponseComponent_eq_zero_of_ne params i j hne,
    finiteCutoffResponseComponent_eq_zero_of_ne params j i (Ne.symm hne)]

/-- Finite broadening interpreted as a Drude transport lifetime through
`η = ℏ / (2 τ_η)`. This is a finite-parameter convention, not a zero-broadening limit. -/
def broadeningTransportLifetime (params : Parameters) : ℝ :=
  params.hbar / (2 * params.broadening)

/-- Normalized Lorentzian factor multiplying the retarded-advanced Green product. -/
def lorentzianNormalization (params : Parameters) : ℝ :=
  params.broadening / Real.pi

/-- Static Kubo trace prefactor used by the finite Drude/Kubo normalization identity. -/
def kuboTracePrefactor (params : Parameters) : ℝ :=
  params.hbar / (2 * Real.pi)

/-- Finite-parameter Drude/Kubo normalization identity. No cutoff, thermodynamic, or
zero-broadening limit is used. -/
theorem broadeningTransportLifetime_mul_lorentzianNormalization_eq_kuboTracePrefactor
    (params : Parameters) (hbroadening : params.broadening ≠ 0) :
    broadeningTransportLifetime params * lorentzianNormalization params =
      kuboTracePrefactor params := by
  unfold broadeningTransportLifetime lorentzianNormalization kuboTracePrefactor
  field_simp [hbroadening, Real.pi_ne_zero]

/-- Pointwise version of the finite Drude/Kubo normalization identity on the named Green weight. -/
theorem broadeningTransportLifetime_mul_lorentzianWeight_eq_kuboWeight
    (params : Parameters) (hbroadening : params.broadening ≠ 0) (p : ℝ) :
    (((broadeningTransportLifetime params * lorentzianNormalization params : ℝ) : ℂ)) *
        retardedAdvancedWeight params p =
      (((kuboTracePrefactor params : ℝ) : ℂ)) * retardedAdvancedWeight params p := by
  rw [broadeningTransportLifetime_mul_lorentzianNormalization_eq_kuboTracePrefactor
    params hbroadening]

end

end QuantumTheory.Transport.Models.Parabolic2DEG
