import LeanCondensedMatter.Transport.Streda.ConductivityNormalization
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.NonCrossing
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRealSpaceIntegral
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossedRadialTrace

set_option linter.style.header false

/-!
# Physically normalized Gaussian crossed Hall contribution

This module is the conductivity-normalization boundary for the regulated massive-Dirac Gaussian
crossed `X` / `Psi` real-space contributions. The upstream Středa layer already attaches the two
Gaussian disorder correlators and each real-space Fourier block already carries its own physical
momentum measure `d²p / (2πℏ)²`. Consequently this layer restores only

- the two physical charge-current scales, giving `(e v)²`; and
- the trace-only Bastin prefactor `ℏ / (2π)`.

It deliberately does not attach `bastinStredaPhysicalMomentumConductivityNormalization`, which would insert an
additional momentum-measure factor. The result remains the regulated ordered measured-`x`,
source-`y` crossed conductivity contribution. No real-space or momentum-cutoff removal,
zero-broadening or weak-disorder limit, closed `X` value, or `Psi = 0` conductivity evaluation is
claimed here.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Physically normalized finite-cutoff finite-broadening ordered-`xy` Gaussian crossed
conductivity contribution.

The two crossed current blocks are built from dimensionless Pauli current vertices upstream, so the
physical current scale contributes `(e v)²`. Their Fourier transforms already contain the physical
momentum measure, hence only `bastinStredaTraceConductivityPrefactor` is attached here. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
    (diagram : GaussianCrossedDiagram)
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) : ℂ :=
  (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
    finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
      diagram v m probeEnergy broadening disorderStrength hbar pMax rMax

/-- The physically normalized crossed Hall contribution reduces to the radial
antisymmetric source-pair trace at finite momentum and real-space cutoffs.
The existing Fourier measures remain inside the radial trace tensor, while
the two disorder correlators and the trace-only Bastin prefactor occur once.
This does not evaluate the radial integral or assert a regulator limit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_eq_radial_antisymmetric_trace
    (diagram : GaussianCrossedDiagram)
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        diagram e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            ((finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
                diagram v m probeEnergy broadening disorderStrength hbar pMax
                radius 0 1 -
              finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor
                diagram v m probeEnergy broadening disorderStrength hbar pMax
                radius 1 0) / 2) := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
    finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRealSpaceIntegral_eq_radial_antisymmetric_trace_of_regulated
    diagram v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  ring

/-- The regulated physical X Hall conductivity is the radial integral of the
three independent transverse-current Pauli minors. The retarded/advanced
Green blocks retain their signed radial arguments, and each Fourier block
already carries its own physical momentum measure. No regulator limit or
closed X value is asserted. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_transverse_radial_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .x e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                0 v m probeEnergy broadening disorderStrength hbar pMax radius
             let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                1 v m probeEnergy broadening disorderStrength hbar pMax radius
             let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
             let GA := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
             let a := InternalSpace.pauliScalarCoefficient Jx
             let b := InternalSpace.pauliScalarCoefficient GR
             let c := InternalSpace.pauliScalarCoefficient Jy
             let d := InternalSpace.pauliScalarCoefficient GA
             let u := InternalSpace.pauliVectorCoefficient Jx
             let vr := InternalSpace.pauliVectorCoefficient GR
             let w := InternalSpace.pauliVectorCoefficient Jy
             let va := InternalSpace.pauliVectorCoefficient GA
             2 * Complex.I *
               ((a * w .y - c * u .y) * (vr .x * va .z - vr .z * va .x) +
                 (b * va .z - d * vr .z) * (w .y * u .x + (u .y) ^ 2) +
                 (d * vr .x - b * va .x) * (w .y * u .z - u .y * w .z))) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_eq_radial_antisymmetric_trace
    .x e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_transverse_minors
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  ring

/-- The finite-regulator X Hall contribution uses the same diagonal-current
K0/K2 difference of squares as Psi. Its mixed isotropic/anisotropic current
moment vanishes algebraically before radial integration. The other X Pauli
minors retain their independent Green and K1 channels; no real-space
integral is evaluated or regulator limit taken. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_diagonal_harmonic_squares_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .x e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                0 v m probeEnergy broadening disorderStrength hbar pMax radius
             let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                1 v m probeEnergy broadening disorderStrength hbar pMax radius
             let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
             let GA := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
             let a := InternalSpace.pauliScalarCoefficient Jx
             let b := InternalSpace.pauliScalarCoefficient GR
             let c := InternalSpace.pauliScalarCoefficient Jy
             let d := InternalSpace.pauliScalarCoefficient GA
             let u := InternalSpace.pauliVectorCoefficient Jx
             let vr := InternalSpace.pauliVectorCoefficient GR
             let w := InternalSpace.pauliVectorCoefficient Jy
             let va := InternalSpace.pauliVectorCoefficient GA
             let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
                v m probeEnergy broadening disorderStrength hbar pMax
             let aA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonScalarCoefficient
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let aR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonScalarCoefficient
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let dA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .z
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let dR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .z
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let bA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .x
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let bR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .x
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let isotropic :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    2 * (p : ℂ) *
                      (polarFourierZerothAngularKernel (p * radius / hbar) *
                        ((aA p * aR p - dA p * dR p) * factor))
             let anisotropic :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    2 * (p : ℂ) *
                      (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                        (bA p * bR p * factor))
             2 * Complex.I *
               ((a * w .y - c * u .y) * (vr .x * va .z - vr .z * va .x) +
                 (b * va .z - d * vr .z) *
                   ((isotropic ^ 2 - anisotropic ^ 2) / 4 + (u .y) ^ 2) +
                 (d * vr .x - b * va .x) * (w .y * u .z - u .y * w .z))) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_transverse_radial_integral
    e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_product_eq_harmonic_squares
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  change
    InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          0 v m probeEnergy broadening disorderStrength hbar pMax radius) .x *
      InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          1 v m probeEnergy broadening disorderStrength hbar pMax radius) .y = _ at hdiag
  rw [mul_comm
    (InternalSpace.pauliVectorCoefficient
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        0 v m probeEnergy broadening disorderStrength hbar pMax radius) .x)
    (InternalSpace.pauliVectorCoefficient
      (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
        1 v m probeEnergy broadening disorderStrength hbar pMax radius) .y)] at hdiag
  dsimp only at hdiag ⊢
  rw [hdiag]

/-- After eliminating the mixed diagonal K0/K2 product, the finite-regulator
physical X Hall integral also substitutes its remaining scalar- and z-current
antisymmetric minors. The scalar minor uses two K1 moments and a K0/K2
diagonal moment; the z minor uses two K0-K2 moments with a common
i*radius/(2*hbar) first-harmonic factor.

Only the transverse K0 current and the retarded/advanced Green minor
channels remain implicit. Their Fourier measures and all physical prefactors
are unchanged; no radial evaluation or regulator limit is asserted. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_first_harmonic_minor_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .x e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                0 v m probeEnergy broadening disorderStrength hbar pMax radius
             let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                1 v m probeEnergy broadening disorderStrength hbar pMax radius
             let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
             let GA := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
             let a := InternalSpace.pauliScalarCoefficient Jx
             let b := InternalSpace.pauliScalarCoefficient GR
             let c := InternalSpace.pauliScalarCoefficient Jy
             let d := InternalSpace.pauliScalarCoefficient GA
             let u := InternalSpace.pauliVectorCoefficient Jx
             let vr := InternalSpace.pauliVectorCoefficient GR
             let w := InternalSpace.pauliVectorCoefficient Jy
             let va := InternalSpace.pauliVectorCoefficient GA
             let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
                v m probeEnergy broadening disorderStrength hbar pMax
             let aA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonScalarCoefficient
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let aR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonScalarCoefficient
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let dA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .z
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let dR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .z
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let bA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .x
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let bR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .x
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let isotropic :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    2 * (p : ℂ) *
                      (polarFourierZerothAngularKernel (p * radius / hbar) *
                        ((aA p * aR p - dA p * dR p) * factor))
             let anisotropic :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    2 * (p : ℂ) *
                      (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                        (bA p * bR p * factor))
             let firstX :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
                      ((aR p * bA p + aA p * bR p) * factor))
             let firstY :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    (p : ℂ) * (polarFourierFirstCosineAngularKernel (p * radius / hbar) *
                      ((-Complex.I * (bR p * dA p - bA p * dR p)) * factor))
             let moment := fun f : ℝ → ℂ =>
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    (p : ℂ) ^ 2 *
                      ((polarFourierZerothAngularKernel (p * radius / hbar) -
                        polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)
             let zX := moment (fun p => (bR p * dA p + bA p * dR p) * factor)
             let zY := moment (fun p => (-Complex.I * (aA p * bR p - aR p * bA p)) * factor)
             let first := Complex.I * (((radius / hbar : ℝ) : ℂ)) / 2
             2 * Complex.I *
               ((firstX * ((isotropic - anisotropic) / 2) - firstY * u .y) *
                   (vr .x * va .z - vr .z * va .x) +
                 (b * va .z - d * vr .z) *
                   ((isotropic ^ 2 - anisotropic ^ 2) / 4 + (u .y) ^ 2) +
                 (d * vr .x - b * va .x) * (first * (w .y * zX - u .y * zY)))) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_diagonal_harmonic_squares_integral
    e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  have hs :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_scalar_diagonal_minor_eq_harmonic_moments
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  have hz :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrent_z_minor_eq_k0_sub_k2
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  change
    InternalSpace.pauliScalarCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          0 v m probeEnergy broadening disorderStrength hbar pMax radius) *
      InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          1 v m probeEnergy broadening disorderStrength hbar pMax radius) .y -
      InternalSpace.pauliScalarCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          1 v m probeEnergy broadening disorderStrength hbar pMax radius) *
      InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          0 v m probeEnergy broadening disorderStrength hbar pMax radius) .y = _ at hs
  change
    InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          1 v m probeEnergy broadening disorderStrength hbar pMax radius) .y *
      InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          0 v m probeEnergy broadening disorderStrength hbar pMax radius) .z -
      InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          0 v m probeEnergy broadening disorderStrength hbar pMax radius) .y *
      InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          1 v m probeEnergy broadening disorderStrength hbar pMax radius) .z = _ at hz
  dsimp only at hs hz ⊢
  rw [hs, hz]

/-- The regulated physical Psi Hall contribution is the finite-radius integral
of its transverse-current-reduced antisymmetric Pauli amplitude and its
complex-conjugate partner. This is a substitution into the canonical
diagram-indexed conductivity boundary, not a claim of Psi cancellation or
of convergence after removing either cutoff. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_transverse_radial_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                0 v m probeEnergy broadening disorderStrength hbar pMax radius
             let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                1 v m probeEnergy broadening disorderStrength hbar pMax radius
             let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
             let a := InternalSpace.pauliScalarCoefficient Jx
             let b := InternalSpace.pauliScalarCoefficient GR
             let c := InternalSpace.pauliScalarCoefficient Jy
             let gx := InternalSpace.pauliVectorCoefficient GR .x
             let gz := InternalSpace.pauliVectorCoefficient GR .z
             let u := InternalSpace.pauliVectorCoefficient Jx
             let w := InternalSpace.pauliVectorCoefficient Jy
             let amplitude := 8 * Complex.I * gz *
                (gx * (a * w .y - c * u .y) -
                  b * ((u .y) ^ 2 + u .x * w .y))
             (amplitude + (starRingEnd ℂ) amplitude) / 2) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_eq_radial_antisymmetric_trace
    .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_transverse_minors
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]

/-- The conjugate-symmetric part of the Psi Pauli triple is a real scalar.
The right-hand side is resolved into the real and imaginary Pauli minor
channels, ready for radial scalar-kernel analysis. -/
private theorem psi_conjugate_triple_half_eq_real_channels (z q : ℂ) :
    (8 * Complex.I * z * q +
        (starRingEnd ℂ) (8 * Complex.I * z * q)) / 2 =
      ((-8 * (z.re * q.im + z.im * q.re) : ℝ) : ℂ) := by
  apply (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.neg_re]
    ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.neg_im]

/-- The physically normalized regulated Psi crossed Hall conductivity is
the radial integral of a *real-valued* minor kernel. In contrast to the
conjugate-symmetrized amplitude representation, the integrand uses only
the real and imaginary parts of two independent scalar products.
No cancellation, radial integration, or cutoff/broadening limit is asserted. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_real_minor_radial_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                0 v m probeEnergy broadening disorderStrength hbar pMax radius
             let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                1 v m probeEnergy broadening disorderStrength hbar pMax radius
             let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
             let a := InternalSpace.pauliScalarCoefficient Jx
             let b := InternalSpace.pauliScalarCoefficient GR
             let c := InternalSpace.pauliScalarCoefficient Jy
             let gx := InternalSpace.pauliVectorCoefficient GR .x
             let gz := InternalSpace.pauliVectorCoefficient GR .z
             let u := InternalSpace.pauliVectorCoefficient Jx
             let w := InternalSpace.pauliVectorCoefficient Jy
             let minor := gx * (a * w .y - c * u .y) -
               b * ((u .y) ^ 2 + u .x * w .y)
             ((-8 * (gz.re * minor.im + gz.im * minor.re) : ℝ) : ℂ)) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_transverse_radial_integral
    e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [psi_conjugate_triple_half_eq_real_channels]

/-- The regulated Psi Hall integrand separates its diagonal-current
product into a difference of the squared K0 and K2 radial moments.
In particular the mixed K0-K2 contribution cancels *before* the outer
real-space radial integration. The transverse K0 current, first-harmonic
current/Green factors and all finite regulators remain explicit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_diagonal_harmonic_squares_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                0 v m probeEnergy broadening disorderStrength hbar pMax radius
             let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
                1 v m probeEnergy broadening disorderStrength hbar pMax radius
             let GR := finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
                .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
             let a := InternalSpace.pauliScalarCoefficient Jx
             let b := InternalSpace.pauliScalarCoefficient GR
             let c := InternalSpace.pauliScalarCoefficient Jy
             let gx := InternalSpace.pauliVectorCoefficient GR .x
             let gz := InternalSpace.pauliVectorCoefficient GR .z
             let u := InternalSpace.pauliVectorCoefficient Jx
             let w := InternalSpace.pauliVectorCoefficient Jy
             let factor := finiteCutoffContinuumBornDysonGaussianCrossedCurrentFactor
                v m probeEnergy broadening disorderStrength hbar pMax
             let aA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonScalarCoefficient
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let aR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonScalarCoefficient
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let dA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .z
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let dR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .z
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let bA := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .x
                  .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let bR := fun p : ℝ =>
                finiteCutoffContinuumBornDysonPauliCoefficient .x
                  .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax
             let isotropic :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    2 * (p : ℂ) *
                      (polarFourierZerothAngularKernel (p * radius / hbar) *
                        ((aA p * aR p - dA p * dR p) * factor))
             let anisotropic :=
                (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
                  ∫ p in (0 : ℝ)..pMax,
                    2 * (p : ℂ) *
                      (polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                        (bA p * bR p * factor))
             let minor := gx * (a * w .y - c * u .y) -
                b * ((u .y) ^ 2 + (isotropic ^ 2 - anisotropic ^ 2) / 4)
             ((-8 * (gz.re * minor.im + gz.im * minor.re) : ℝ) : ℂ)) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_real_minor_radial_integral
    e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  have hdiag :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialCurrentPauliCoefficient_diagonal_product_eq_harmonic_squares
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  change
    InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          0 v m probeEnergy broadening disorderStrength hbar pMax radius) .x *
      InternalSpace.pauliVectorCoefficient
        (finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
          1 v m probeEnergy broadening disorderStrength hbar pMax radius) .y = _ at hdiag
  dsimp only at hdiag ⊢
  rw [hdiag]

/-- The physically normalized finite-cutoff finite-broadening Gaussian crossed correction.

The two leading crossed topologies remain indexed upstream, but their physical response is exposed
through one additive boundary here. This keeps the `X` / `Psi` decomposition available for later
evaluation while giving downstream Hall consumers one object for the complete Gaussian crossed
correction. No crossed topology is absorbed into the non-crossing ladder by this definition. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) : ℂ :=
  ∑ diagram : GaussianCrossedDiagram,
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
      diagram e v m probeEnergy broadening disorderStrength hbar pMax rMax

/-- The total regulated crossed correction is exactly the sum of its `X` and `Psi` topology
contributions. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal_eq_x_add_psi
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal
        e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .x e v m probeEnergy broadening disorderStrength hbar pMax rMax +
      finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal
  exact sum_gaussianCrossedDiagram _

/-- The regulated crossed conductivity vanishes identically when the Gaussian disorder strength is
zero because the two explicit crossed disorder correlators supply a factor `disorderStrength²`. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_zero_disorder
    (diagram : GaussianCrossedDiagram)
    (e v m probeEnergy broadening hbar pMax rMax : ℝ) :
  finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
      diagram e v m probeEnergy broadening 0 hbar pMax rMax = 0 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity]

/-- The total regulated crossed correction vanishes at zero Gaussian disorder strength. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal_zero_disorder
    (e v m probeEnergy broadening hbar pMax rMax : ℝ) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal
      e v m probeEnergy broadening 0 hbar pMax rMax = 0 := by
  simp [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivityTotal]

/-- The regulated `Psi` conductivity remains real because its trace-level Hermitian-conjugate
partner is included upstream and the remaining physical normalization is real. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_im
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ) :
    (finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
      .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax).im = 0 := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
  rw [Complex.mul_im,
    finiteCutoffContinuumBornDysonGaussianCrossedWeightedRealSpaceIntegral_psi_im]
  simp only [Complex.ofReal_im, mul_zero, zero_mul, add_zero]


/-- The exact closed-form crossed correction required to turn the proved non-crossing Ado result
into the full Gaussian-disorder Ado benchmark.

This is an algebraic *target identity*, not an evaluation of either crossed trace integral:
the finite-regulator `X` and `Psi` kernels still require their own analytical limits. The
correction on the left is the required sum of those contributions after taking those limits.
In particular, the statement does not assert `Psi = 0` or identify an unevaluated crossed
integral with this expression. -/
theorem nonCrossingHallConductivity_add_gaussianCrossedTarget_eq_gaussianBenchmark
    (e hbar m probeEnergy : ℝ) :
    nonCrossingHallConductivity e hbar m probeEnergy +
        (4 * e ^ 2 / planckFromReduced hbar) *
          (probeEnergy * m * (probeEnergy ^ 2 - m ^ 2) /
            (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) =
      -(8 * e ^ 2 / planckFromReduced hbar) *
        (probeEnergy * m ^ 3 /
          (probeEnergy ^ 2 + 3 * m ^ 2) ^ 2) := by
  unfold nonCrossingHallConductivity
  ring

end

end QuantumTheory.Models.MassiveDirac
