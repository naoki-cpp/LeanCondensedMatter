import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRealSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Finite-radius real-space integration of Gaussian crossed Hall kernels

This module lifts the finite-cutoff finite-broadening crossed trace kernel to the real-space integral
appearing before the closed `X` / `Psi` evaluations. The two-dimensional position integral is kept in
polar form with an explicit finite radial cutoff,

```text
∫ d²r K(r) = ∫₀^{rMax} ρ dρ ∫₀^{2π} dφ K(ρ cos φ, ρ sin φ).
```

A separate weighted boundary multiplies this integral by the two scalar Gaussian disorder
correlators carried by a crossed diagram. In the repository normalization each correlator contributes
one factor of `disorderStrength`, so the crossed pair contributes `disorderStrength²`. This is the
finite-regulator counterpart of the squared disorder factor in Ado et al., EPL 111, 37004 (2015),
Eq. (13), before restoring the remaining physical conductivity normalization. The Fourier blocks
upstream already include the physical momentum measure `d²p / (2πℏ)²`, so downstream conductivity
normalization must not attach `momentumMeasurePrefactor hbar` a second time. In the massive-Dirac
normalization API the remaining scalar boundary is therefore the trace-only
`bastinStredaTraceConductivityPrefactor`, not `bastinStredaPhysicalMomentumConductivityNormalization`, which would attach a
second momentum measure.

No infinite-radius limit, momentum-cutoff removal, zero-broadening or weak-disorder limit,
Bessel-function reduction, or closed crossed conductivity is claimed here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open MeasureTheory
open scoped Interval

/-- An interval integral of a pointwise real complex-valued field is again real. Kept private because
it is only proof infrastructure for the crossed `Psi` reality statements below. -/
private theorem intervalIntegral_im_eq_zero_of_forall
    {f : ℝ → ℂ} {a b : ℝ} (h : ∀ x, (f x).im = 0) :
    (∫ x in a..b, f x).im = 0 := by
  by_cases hf : IntervalIntegrable f volume a b
  · change RCLike.im (∫ x in a..b, f x) = 0
    rw [← intervalIntegral.intervalIntegral_im hf]
    simp [h]
  · rw [intervalIntegral.integral_undef hf]
    simp

/-- Finite-radius polar integral of a complex field over two-dimensional real space. The Jacobian
`ρ` is explicit and there is no momentum-space normalization factor in this position-space measure. -/
private noncomputable def finiteRadiusPolarRealSpaceIntegral
    (rMax : ℝ) (field : (Fin 2 → ℝ) → ℂ) : ℂ :=
  ∫ radius in (0 : ℝ)..rMax,
    ∫ angle in (0 : ℝ)..(2 * Real.pi),
      ((radius : ℂ) * field (polarPoint2D radius angle))

/-- Finite-radius integral of the model-specific finite-cutoff finite-`η` Gaussian crossed trace
kernel. This is the regulated real-space integral underlying Ado et al. Eq. (13), before the two
crossed disorder correlators and the physical conductivity normalization are attached. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) : ℂ :=
  finiteRadiusPolarRealSpaceIntegral rMax
    (finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
      diagram v m probeEnergy broadening disorderStrength hbar pMax)

/-- Finite real-space angular integration extracts only the constant harmonic of
the *full* crossed trace kernel. The supplied expansion is over the actual
polar real-space point, not merely the radial-axis restriction.

This is an exact finite-regulator reduction conditional on a pointwise angular
harmonic representation; proving that representation for the model's X/Psi
traces and evaluating the remaining radial integral are separate tasks. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_eq_radial_harmonic_constant
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (coefficients : ℝ → AngularHarmonicCoefficients ℂ)
    (hangle : ∀ radius angle : ℝ,
      finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
          diagram v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius angle) =
        (coefficients radius).eval angle) :
    finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
        diagram v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) * (coefficients radius).constant := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
    finiteRadiusPolarRealSpaceIntegral
  simp_rw [hangle]
  calc
    (∫ radius in (0 : ℝ)..rMax,
      ∫ angle in (0 : ℝ)..(2 * Real.pi),
        (radius : ℂ) * (coefficients radius).eval angle) =
        ∫ radius in (0 : ℝ)..rMax,
          (((2 * Real.pi : ℝ) : ℂ)) *
            ((radius : ℂ) * (coefficients radius).constant) := by
      apply intervalIntegral.integral_congr
      intro radius _
      dsimp only
      rw [intervalIntegral.integral_const_mul,
        (coefficients radius).integral_eval]
      simp; ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- Bilinear angular projection for the Cartesian `xy` response under a planar
rotation. The constant angular coefficient is the antisymmetric part of the
radial rank-two trace tensor, not its `xy` entry alone. -/
private def gaussianCrossedAngularTensorCoefficients
    (tensor : Fin 2 → Fin 2 → ℂ) : AngularHarmonicCoefficients ℂ :=
  { constant := (tensor 0 1 - tensor 1 0) / 2
    firstCosine := 0
    firstSine := 0
    secondCosine := (tensor 0 1 + tensor 1 0) / 2
    secondMixed := tensor 0 0 - tensor 1 1 }

/-- A rotated `xy` rank-two tensor contains only the constant and second
angular harmonics. Its angular average projects onto the antisymmetric
`xy-yx` sector. -/
private theorem gaussianCrossedAngularTensorCoefficients_eval
    (tensor : Fin 2 → Fin 2 → ℂ) (angle : ℝ) :
    (gaussianCrossedAngularTensorCoefficients tensor).eval angle =
      (((Real.cos angle : ℝ) : ℂ) ^ 2) * tensor 0 1 -
        (((Real.sin angle : ℝ) : ℂ) ^ 2) * tensor 1 0 +
        (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
          (tensor 0 0 - tensor 1 1) := by
  have htrig :
      (((Real.sin angle : ℝ) : ℂ) ^ 2) +
        (((Real.cos angle : ℝ) : ℂ) ^ 2) = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  simp only [gaussianCrossedAngularTensorCoefficients,
    AngularHarmonicCoefficients.eval, smul_eq_mul, mul_zero,
    add_zero]
  linear_combination -((tensor 0 1 - tensor 1 0) / 2) * htrig

/-- Source-pair-indexed radial X/Psi trace tensor. The existing radial trace
uses only the `xy` entry; the angular average also requires the `yx` entry.
The two Green functions and both real-space current blocks are the canonical
finite-cutoff Born-Dyson objects, with no new normalization. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (measured source : Fin 2) : ℂ :=
  gaussianCrossedTraceKernel diagram
    (fun ρ =>
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        .retarded v m probeEnergy broadening disorderStrength hbar pMax ρ)
    (fun ρ =>
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        .advanced v m probeEnergy broadening disorderStrength hbar pMax ρ)
    (fun axis ρ =>
      finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        (if axis = 0 then measured else source)
        v m probeEnergy broadening disorderStrength hbar pMax ρ)
    radius

/-- If the full angular crossed trace transforms as the `xy` component of
its canonical radial source-pair trace tensor under SO(2), the *complete*
finite-radius real-space integral is the radial integral of the antisymmetric
`xy-yx` sector.

The rotation-covariance hypothesis is explicit: it is not implied by the
previously proved radial-axis Fourier identities and must be discharged from
the model's Green/current rotation laws. This theorem performs the angular
projection, not the remaining radial or regulator limits. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_eq_radial_antisymmetric_trace
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hrotation : ∀ radius angle : ℝ,
      let tensor := finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        diagram v m probeEnergy broadening disorderStrength hbar pMax radius
      finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
          diagram v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius angle) =
        (((Real.cos angle : ℝ) : ℂ) ^ 2) * tensor 0 1 -
          (((Real.sin angle : ℝ) : ℂ) ^ 2) * tensor 1 0 +
          (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
            (tensor 0 0 - tensor 1 1)) :
    finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
        diagram v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            ((finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
                diagram v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
              finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
                diagram v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2) := by
  apply finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_eq_radial_harmonic_constant
    diagram v m probeEnergy broadening disorderStrength hbar pMax rMax
    (fun radius => gaussianCrossedAngularTensorCoefficients
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        diagram v m probeEnergy broadening disorderStrength hbar pMax radius))
  intro radius angle
  rw [hrotation radius angle]
  exact (gaussianCrossedAngularTensorCoefficients_eval
    (finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
      diagram v m probeEnergy broadening disorderStrength hbar pMax radius) angle).symm

/-- The finite-radius `Psi` integral remains real because its pointwise trace kernel is real. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_psi_im
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
      .psi v m probeEnergy broadening disorderStrength hbar pMax rMax).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
    finiteRadiusPolarRealSpaceIntegral
  apply intervalIntegral_im_eq_zero_of_forall
  intro radius
  apply intervalIntegral_im_eq_zero_of_forall
  intro angle
  simp [Complex.mul_im]

/-- Crossed real-space trace integral with the two Gaussian disorder correlators attached.

The Born disorder parameter is the scalar two-point correlator amplitude used throughout the
massive-Dirac disorder stack. A crossed `X` or `Psi` diagram contains two such correlator lines, so
this boundary multiplies the regulated trace integral by `disorderStrength²`. Charge/current and
`e² / h` conductivity normalization remain downstream. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) : ℂ :=
  (((disorderStrength ^ 2 : ℝ) : ℂ)) *
    finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
      diagram v m probeEnergy broadening disorderStrength hbar pMax rMax

/-- The explicit real disorder-pair weight preserves the reality of the regulated `Psi` integral. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral_psi_im
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
      .psi v m probeEnergy broadening disorderStrength hbar pMax rMax).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
  rw [Complex.mul_im,
    finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_psi_im]
  simp only [Complex.ofReal_im, mul_zero, zero_mul, add_zero]

/-- With the two crossed disorder correlators explicit, the regulated crossed contribution vanishes
identically at zero disorder strength. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral_zero_disorder
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening hbar pMax rMax : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
      diagram v m probeEnergy broadening 0 hbar pMax rMax = 0 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral]

end

end QuantumTheory.Models.MassiveDirac
