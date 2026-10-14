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

/-- The physically relevant antisymmetric radial source tensor reduces,
without regulator assumptions, to one X trace of a difference or one Psi
trace-difference amplitude plus its Hermitian-conjugate partner. This is the
exact remaining matrix algebra to be evaluated after angular projection. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_antisymmetric_eq
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    let greenR : ℝ → Matrix2 := fun ρ =>
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        .retarded v m probeEnergy broadening disorderStrength hbar pMax ρ
    let greenA : ℝ → Matrix2 := fun ρ =>
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        .advanced v m probeEnergy broadening disorderStrength hbar pMax ρ
    let current : Fin 2 → ℝ → Matrix2 := fun source ρ =>
      finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        source v m probeEnergy broadening disorderStrength hbar pMax ρ
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        diagram v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        diagram v m probeEnergy broadening disorderStrength hbar pMax radius 1 0 =
      match diagram with
      | .x =>
          Matrix.trace
            ((current 0 radius * greenR (-radius) * current 1 radius -
                current 1 radius * greenR (-radius) * current 0 radius) *
              greenA (-radius))
      | .psi =>
          let amplitude := Matrix.trace
            (current 0 radius * greenR (-radius) * greenR radius * current 1 (-radius) -
              current 1 radius * greenR (-radius) * greenR radius * current 0 (-radius))
          amplitude + (starRingEnd ℂ) amplitude := by
  dsimp only
  let greenR : ℝ → Matrix2 := fun ρ =>
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      .retarded v m probeEnergy broadening disorderStrength hbar pMax ρ
  let greenA : ℝ → Matrix2 := fun ρ =>
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      .advanced v m probeEnergy broadening disorderStrength hbar pMax ρ
  let current : Fin 2 → ℝ → Matrix2 := fun source ρ =>
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
      source v m probeEnergy broadening disorderStrength hbar pMax ρ
  have hxy :
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
          diagram v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 =
        gaussianCrossedTraceKernel diagram greenR greenA current radius := by
    change gaussianCrossedTraceKernel diagram greenR greenA
      (fun axis ρ => current (if axis = 0 then 0 else 1) ρ) radius = _
    congr 1
    funext axis ρ
    fin_cases axis <;> rfl
  have hyx :
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
          diagram v m probeEnergy broadening disorderStrength hbar pMax radius 1 0 =
        gaussianCrossedTraceKernel diagram greenR greenA
          (fun axis ρ => if axis = 0 then current 1 ρ else current 0 ρ) radius := by
    change gaussianCrossedTraceKernel diagram greenR greenA
      (fun axis ρ => current (if axis = 0 then 1 else 0) ρ) radius = _
    congr 1
    funext axis ρ
    fin_cases axis <;> rfl
  rw [hxy, hyx]
  cases diagram with
  | x =>
      exact gaussianCrossedTraceKernel_x_sub_swapped greenR greenA current radius
  | psi =>
      exact gaussianCrossedTraceKernel_psi_sub_swapped greenR greenA current radius

/-- The antisymmetric finite-regulator X radial trace contains only oriented
Pauli triple products, with the symmetric Pauli-coefficient terms cancelled.
This is a pointwise identity in the radial coordinate, not yet an evaluation
of the remaining real-space integral or regulator limits. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_pauli_triples
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
      0 v m probeEnergy broadening disorderStrength hbar pMax radius
    let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
      1 v m probeEnergy broadening disorderStrength hbar pMax radius
    let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
    let GA := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
        .x v m probeEnergy broadening disorderStrength hbar pMax radius 1 0 =
      4 * Complex.I *
        (InternalSpace.pauliScalarCoefficient Jx *
            dotProduct (InternalSpace.pauliVectorCoefficient GR)
              (InternalSpace.pauliCross (InternalSpace.pauliVectorCoefficient Jy)
                (InternalSpace.pauliVectorCoefficient GA)) +
          InternalSpace.pauliScalarCoefficient GR *
            dotProduct (InternalSpace.pauliVectorCoefficient Jx)
              (InternalSpace.pauliCross (InternalSpace.pauliVectorCoefficient Jy)
                (InternalSpace.pauliVectorCoefficient GA)) +
          InternalSpace.pauliScalarCoefficient Jy *
            dotProduct
              (InternalSpace.pauliCross (InternalSpace.pauliVectorCoefficient Jx)
                (InternalSpace.pauliVectorCoefficient GR))
              (InternalSpace.pauliVectorCoefficient GA) +
          InternalSpace.pauliScalarCoefficient GA *
            dotProduct
              (InternalSpace.pauliCross (InternalSpace.pauliVectorCoefficient Jx)
                (InternalSpace.pauliVectorCoefficient GR))
              (InternalSpace.pauliVectorCoefficient Jy)) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_antisymmetric_eq
    .x v m probeEnergy broadening disorderStrength hbar pMax radius]
  dsimp only
  rw [Matrix.sub_mul, Matrix.trace_sub]
  exact InternalSpace.trace_four_antisymmetric_eq_pauliCoefficients _ _ _ _

/-- A common in-plane spinor conjugation of the Green and current blocks
cancels inside either Gaussian crossed trace topology, including the
Hermitian-conjugate partner in the Psi diagram. -/
private theorem gaussianCrossedTraceKernel_spinRotation_conjugate
    (diagram : GaussianCrossedDiagram)
    (greenRetarded greenAdvanced : ℝ → Matrix2)
    (current : Fin 2 → ℝ → Matrix2)
    (radius angle : ℝ) :
    gaussianCrossedTraceKernel diagram
        (fun ρ => inPlaneSpinRotation angle * greenRetarded ρ *
          inPlaneSpinRotationInverse angle)
        (fun ρ => inPlaneSpinRotation angle * greenAdvanced ρ *
          inPlaneSpinRotationInverse angle)
        (fun source ρ => inPlaneSpinRotation angle * current source ρ *
          inPlaneSpinRotationInverse angle) radius =
      gaussianCrossedTraceKernel diagram greenRetarded greenAdvanced current radius := by
  have htrace (A B C D : Matrix2) :
      Matrix.trace
        ((inPlaneSpinRotation angle * A * inPlaneSpinRotationInverse angle) *
          (inPlaneSpinRotation angle * B * inPlaneSpinRotationInverse angle) *
          (inPlaneSpinRotation angle * C * inPlaneSpinRotationInverse angle) *
          (inPlaneSpinRotation angle * D * inPlaneSpinRotationInverse angle)) =
        Matrix.trace (A * B * C * D) := by
    rw [inPlaneSpinRotation_conjugate_mul angle A B,
      inPlaneSpinRotation_conjugate_mul angle (A * B) C,
      inPlaneSpinRotation_conjugate_mul angle (A * B * C) D,
      inPlaneSpinRotation_conjugate_trace]
  cases diagram with
  | x =>
      simpa only [gaussianCrossedTraceKernel] using
        htrace (current 0 radius) (greenRetarded (-radius))
          (current 1 radius) (greenAdvanced (-radius))
  | psi =>
      have h := htrace (current 0 radius) (greenRetarded (-radius))
        (greenRetarded radius) (current 1 (-radius))
      simpa only [gaussianCrossedTraceKernel] using
        congrArg (fun z : ℂ => z + (starRingEnd ℂ) z) h

/-- Exact SO(2) rotation of the full Gaussian X/Psi trace, expressed in the
canonical radial source-pair tensor. Both current insertions are rotated,
while their common spinor conjugations cancel under the trace. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel_polarPoint2D_eq_radial_tensor
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax radius angle : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let tensor := finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
      diagram v m probeEnergy broadening disorderStrength hbar pMax radius
    finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
        diagram v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius angle) =
      (((Real.cos angle : ℝ) : ℂ) ^ 2) * tensor 0 1 -
        (((Real.sin angle : ℝ) : ℂ) ^ 2) * tensor 1 0 +
        (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
          (tensor 0 0 - tensor 1 1) := by
  let U := inPlaneSpinRotation angle
  let Ui := inPlaneSpinRotationInverse angle
  let greenR : ℝ → Matrix2 := fun ρ =>
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      .retarded v m probeEnergy broadening disorderStrength hbar pMax ρ
  let greenA : ℝ → Matrix2 := fun ρ =>
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      .advanced v m probeEnergy broadening disorderStrength hbar pMax ρ
  let current : Fin 2 → ℝ → Matrix2 := fun source ρ =>
    finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
      source v m probeEnergy broadening disorderStrength hbar pMax ρ
  let rotated : Fin 2 → ℝ → Matrix2 := fun source ρ =>
    if source = 0 then
      (((Real.cos angle : ℝ) : ℂ)) • current 0 ρ -
        (((Real.sin angle : ℝ) : ℂ)) • current 1 ρ
    else
      (((Real.sin angle : ℝ) : ℂ)) • current 0 ρ +
        (((Real.cos angle : ℝ) : ℂ)) • current 1 ρ
  have hR (ρ : ℝ) :
      finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
          .retarded v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D ρ angle) = U * greenR ρ * Ui :=
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_polarPoint2D_eq_radial_spinRotation
      .retarded v m probeEnergy broadening disorderStrength hbar pMax ρ angle
  have hA (ρ : ℝ) :
      finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
          .advanced v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D ρ angle) = U * greenA ρ * Ui :=
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_polarPoint2D_eq_radial_spinRotation
      .advanced v m probeEnergy broadening disorderStrength hbar pMax ρ angle
  have hJ (source : Fin 2) (ρ : ℝ) :
      finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock
          source v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D ρ angle) = U * rotated source ρ * Ui := by
    simpa only [U, Ui, rotated, current] using
      (finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceCurrentBlock_polarPoint2D_sourceRotation
        source v m probeEnergy broadening disorderStrength hbar pMax ρ angle
        hbroadening hdisorder hpMax)
  have hposition : -(polarPoint2D radius angle) =
      polarPoint2D (-radius) angle := neg_polarPoint2D radius angle
  have hbridge :
      finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
          diagram v m probeEnergy broadening disorderStrength hbar pMax
          (polarPoint2D radius angle) =
        gaussianCrossedTraceKernel diagram
          (fun ρ => U * greenR ρ * Ui)
          (fun ρ => U * greenA ρ * Ui)
          (fun source ρ => U * rotated source ρ * Ui) radius := by
    cases diagram with
    | x =>
        simp only [finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel,
          gaussianCrossedTraceKernel]
        rw [hposition, hJ 0 radius, hJ 1 radius, hR (-radius), hA (-radius)]
    | psi =>
        simp only [finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel,
          gaussianCrossedTraceKernel]
        rw [hposition, hJ 0 radius, hJ 1 (-radius), hR (-radius), hR radius]
  calc
    finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel
        diagram v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius angle) =
      gaussianCrossedTraceKernel diagram greenR greenA rotated radius := by
        rw [hbridge]
        exact gaussianCrossedTraceKernel_spinRotation_conjugate
          diagram greenR greenA rotated radius angle
    _ = _ := by
      rw [gaussianCrossedTraceKernel_rotated_sources
        diagram greenR greenA current radius (Real.cos angle) (Real.sin angle)]
      rfl

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

/-- The regulated Gaussian X/Psi real-space integral reduces unconditionally to
the antisymmetric radial source-pair tensor once the finite-broadening
integrability assumptions are supplied. This discharges the former
model-specific angular-rotation hypothesis using the proved Green/current
SO(2) covariance, without taking any regulator limit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_eq_radial_antisymmetric_trace_of_regulated
    (diagram : GaussianCrossedDiagram)
    (v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral
        diagram v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            ((finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
                diagram v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
              finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
                diagram v m probeEnergy broadening disorderStrength hbar pMax radius 1 0) / 2) := by
  apply finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_eq_radial_antisymmetric_trace
    diagram v m probeEnergy broadening disorderStrength hbar pMax rMax
  intro radius angle
  exact finiteCutoffContinuumBornDysonGaussianCrossedTraceKernel_polarPoint2D_eq_radial_tensor
    diagram v m probeEnergy broadening disorderStrength hbar pMax radius angle
    hbroadening hdisorder hpMax

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
