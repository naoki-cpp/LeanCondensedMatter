import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Models.Parabolic2DEG.Model
import LeanCondensedMatter.Transport.Streda.RetardedAdvanced
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-cutoff finite-broadening parabolic-2DEG response

This module owns the radial/angular reduction and normalization boundary for the parabolic benchmark.
The finite response keeps `p_max`, `η`, and the momentum-measure normalization explicit. The
Green-function response factor is not an RA bubble invented locally: it is the canonical finite
Středa surface primitive `RA - (RR + AA)/2` supplied by `Transport.Streda.RetardedAdvanced`.

The raw finite-cutoff response and the physical conductivity boundary are distinct. The raw response
contains the explicit momentum-measure normalization; the conductivity tensor additionally receives
the named static Kubo trace prefactor `ℏ/(2π)`.

The off-diagonal cancellation proved below is a consequence of the isotropic angular harmonics of
this benchmark. It is not a claim about a generic two-dimensional system and does not introduce a
nonzero Hall response.
-/

namespace QuantumTheory.Transport.Models.Parabolic2DEG

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Canonical physical-momentum measure normalization `1/(2πℏ)²`. Parameters keep the actual
chosen normalization explicit, so consumers may compare it with this named convention. -/
def canonicalMomentumMeasureNormalization (params : Parameters) : ℝ :=
  momentumMeasurePrefactor params.hbar

/-- Predicate stating that the explicitly stored measure normalization is the canonical
two-dimensional physical-momentum convention. -/
def UsesCanonicalMomentumMeasure (params : Parameters) : Prop :=
  params.momentumMeasureNormalization = canonicalMomentumMeasureNormalization params

/-- Radial current scale before angular projection, routed through the model's named current
component rather than reconstructing the charge/velocity normalization in the response layer. -/
def radialCurrentScale (params : Parameters) (p : ℝ) : ℝ :=
  currentComponent params 0 p 0

@[simp]
theorem radialCurrentScale_eq (params : Parameters) (p : ℝ) :
    radialCurrentScale params p =
      params.signedCharge * p / params.effectiveMass := by
  simp [radialCurrentScale, currentComponent, velocityComponent, momentumComponent]
  ring

/-- On a polar momentum circle, every Cartesian current component is the named radial current scale
times the corresponding sine/cosine factor. This pins the angular reduction to the model current
convention. -/
theorem currentComponent_polar
    (params : Parameters) (direction : Fin 2) (p θ : ℝ) :
    currentComponent params direction (p * Real.cos θ) (p * Real.sin θ) =
      radialCurrentScale params p *
        (if direction = 0 then Real.cos θ else Real.sin θ) := by
  fin_cases direction <;>
    simp [radialCurrentScale, currentComponent, velocityComponent, momentumComponent] <;>
    ring

/-- Canonical constant/second-harmonic representation of the product of two Cartesian current
components on a circle of radius `p`.

For equal directions the constant piece is one half of `(q p / m_eff)²`; the second-cosine
coefficient distinguishes `xx` from `yy`. For unequal directions the product is purely the mixed
second harmonic. The common current scale is obtained from `currentComponent`. -/
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

/-- Pointwise clean finite-broadening Středa surface kernel using the model's named current and
Green operators. This is the direct model-to-common-response seam before angular/radial reduction. -/
noncomputable def stredaSurfacePointKernel
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) : ℂ :=
  suppliedGreenStredaSurfacePrimitiveTraceKernel
    (currentOperator params measured px py)
    (greenOperator .retarded params px py)
    (currentOperator params source px py)
    (greenOperator .advanced params px py)

/-- The model point kernel is exactly the generic clean regularized Středa surface primitive. -/
theorem stredaSurfacePointKernel_eq_regularized
    (params : Parameters) (measured source : Fin 2) (px py : ℝ) :
    stredaSurfacePointKernel params measured source px py =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator params px py)
        (currentOperator params measured px py)
        (currentOperator params source px py)
        params.chemicalPotential params.broadening := by
  symm
  simpa [stredaSurfacePointKernel, greenOperator, retardedResolvent, advancedResolvent] using
    (regularizedStredaSurfacePrimitiveTrace_eq_suppliedGreen
      (hamiltonianOperator params px py)
      (currentOperator params measured px py)
      (currentOperator params source px py)
      params.chemicalPotential params.broadening)

/-- Radial Green-sector weight of the clean Středa surface primitive. Current factors are replaced
by identities here because their complete angular dependence is owned separately by
`currentProductAngularCoefficients`. -/
noncomputable def stredaSurfaceGreenWeight (params : Parameters) (p : ℝ) : ℂ :=
  suppliedGreenStredaSurfacePrimitiveTraceKernel
    (1 : BandHilbert →L[ℂ] BandHilbert)
    (greenOperator .retarded params p 0)
    (1 : BandHilbert →L[ℂ] BandHilbert)
    (greenOperator .advanced params p 0)

/-- The radial Green-sector weight is itself a specialization of the generic regularized Středa
surface primitive, rather than an RA-only approximation. -/
theorem stredaSurfaceGreenWeight_eq_regularized
    (params : Parameters) (p : ℝ) :
    stredaSurfaceGreenWeight params p =
      regularizedStredaSurfacePrimitiveTrace
        (hamiltonianOperator params p 0)
        (1 : BandHilbert →L[ℂ] BandHilbert)
        (1 : BandHilbert →L[ℂ] BandHilbert)
        params.chemicalPotential params.broadening := by
  symm
  simpa [stredaSurfaceGreenWeight, greenOperator, retardedResolvent, advancedResolvent] using
    (regularizedStredaSurfacePrimitiveTrace_eq_suppliedGreen
      (hamiltonianOperator params p 0)
      (1 : BandHilbert →L[ℂ] BandHilbert)
      (1 : BandHilbert →L[ℂ] BandHilbert)
      params.chemicalPotential params.broadening)

/-- Radial finite-broadening Středa surface kernel after full-angle reduction. The leading `p`
is the polar Jacobian; current and Green normalizations are each attached at one named boundary. -/
noncomputable def finiteBroadeningRadialKernel
    (params : Parameters) (measured source : Fin 2) (p : ℝ) : ℂ :=
  ((p : ℝ) : ℂ) *
    angularIntegratedCurrentProduct params measured source p *
      stredaSurfaceGreenWeight params p

/-- Finite-cutoff, finite-broadening ordered response component before the Kubo trace prefactor.
The explicit momentum-measure normalization is attached exactly once here. -/
noncomputable def finiteCutoffResponseComponent
    (params : Parameters) (measured source : Fin 2) : ℂ :=
  ((params.momentumMeasureNormalization : ℝ) : ℂ) *
    ∫ p : ℝ in (0 : ℝ)..params.momentumCutoff,
      finiteBroadeningRadialKernel params measured source p

/-- Static Kubo/Středa trace prefactor attached only when the finite response is promoted to a
physical conductivity. -/
def kuboTracePrefactor (params : Parameters) : ℝ :=
  params.hbar / (2 * Real.pi)

/-- Finite-cutoff conductivity component obtained from the raw model response by the named Kubo
trace normalization. -/
noncomputable def finiteCutoffConductivityComponent
    (params : Parameters) (measured source : Fin 2) : ℂ :=
  ((kuboTracePrefactor params : ℝ) : ℂ) *
    finiteCutoffResponseComponent params measured source

/-- Common physical conductivity seam for the finite parabolic benchmark. -/
noncomputable def finiteCutoffConductivityTensor
    (params : Parameters) : ConductivityTensor (Fin 2) where
  component := finiteCutoffConductivityComponent params

@[simp]
theorem finiteCutoffConductivityTensor_component
    (params : Parameters) (measured source : Fin 2) :
    (finiteCutoffConductivityTensor params).component measured source =
      finiteCutoffConductivityComponent params measured source := rfl

/-- The isotropic current product has no constant angular harmonic for unequal directions. -/
theorem angularIntegratedCurrentProduct_eq_zero_of_ne
    (params : Parameters) (measured source : Fin 2) (hne : measured ≠ source) (p : ℝ) :
    angularIntegratedCurrentProduct params measured source p = 0 := by
  simp [angularIntegratedCurrentProduct, currentProductAngularCoefficients, hne]

/-- Under the explicit off-diagonal hypothesis, the finite isotropic raw response vanishes. -/
theorem finiteCutoffResponseComponent_eq_zero_of_ne
    (params : Parameters) (measured source : Fin 2) (hne : measured ≠ source) :
    finiteCutoffResponseComponent params measured source = 0 := by
  unfold finiteCutoffResponseComponent finiteBroadeningRadialKernel
  simp [angularIntegratedCurrentProduct_eq_zero_of_ne params measured source hne]

/-- Under the explicit off-diagonal hypothesis, the normalized conductivity component vanishes. -/
theorem finiteCutoffConductivityComponent_eq_zero_of_ne
    (params : Parameters) (measured source : Fin 2) (hne : measured ≠ source) :
    finiteCutoffConductivityComponent params measured source = 0 := by
  simp [finiteCutoffConductivityComponent,
    finiteCutoffResponseComponent_eq_zero_of_ne params measured source hne]

/-- Under the explicit off-diagonal hypothesis, the Hall projection of the isotropic benchmark
vanishes. -/
theorem finiteCutoffConductivityTensor_hallComponent_eq_zero_of_ne
    (params : Parameters) (i j : Fin 2) (hne : i ≠ j) :
    (finiteCutoffConductivityTensor params).hallComponent i j = 0 := by
  rw [ConductivityTensor.hallComponent]
  simp [finiteCutoffConductivityComponent_eq_zero_of_ne params i j hne,
    finiteCutoffConductivityComponent_eq_zero_of_ne params j i (Ne.symm hne)]

/-- Finite broadening interpreted as a transport lifetime through the linewidth convention
`η = ℏ / (2 τ_η)`. This is a finite-parameter convention, not a zero-broadening limit; it matches
the standard single-particle retarded self-energy convention `Σᴿ = -iℏ/(2τ)`; see G. D. Mahan,
*Many-Particle Physics*, 3rd ed. (Kluwer/Plenum, 2000), for the impurity-broadened Green-function
linewidth convention. -/
def broadeningTransportLifetime (params : Parameters) : ℝ :=
  params.hbar / (2 * params.broadening)

/-- Lorentzian normalization associated with the same finite broadening. -/
def lorentzianNormalization (params : Parameters) : ℝ :=
  params.broadening / Real.pi

/-- Finite-parameter Drude/Kubo normalization identity under the model's explicit physical
regularity assumptions. No cutoff, thermodynamic, or zero-broadening limit is used. -/
theorem broadeningTransportLifetime_mul_lorentzianNormalization_eq_kuboTracePrefactor
    (params : Parameters) (hregular : params.IsRegular) :
    broadeningTransportLifetime params * lorentzianNormalization params =
      kuboTracePrefactor params := by
  unfold broadeningTransportLifetime lorentzianNormalization kuboTracePrefactor
  field_simp [hregular.broadening_ne_zero, Real.pi_ne_zero]

/-- Pointwise version of the finite Drude/Kubo normalization identity on the canonical Středa
surface Green-sector weight. -/
theorem broadeningTransportLifetime_mul_lorentzianWeight_eq_kuboWeight
    (params : Parameters) (hregular : params.IsRegular) (p : ℝ) :
    (((broadeningTransportLifetime params * lorentzianNormalization params : ℝ) : ℂ)) *
        stredaSurfaceGreenWeight params p =
      (((kuboTracePrefactor params : ℝ) : ℂ)) * stredaSurfaceGreenWeight params p := by
  rw [broadeningTransportLifetime_mul_lorentzianNormalization_eq_kuboTracePrefactor
    params hregular]

end

end QuantumTheory.Transport.Models.Parabolic2DEG
