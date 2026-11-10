import LeanCondensedMatter.Transport.Streda.ConductivityNormalization
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.GaussianCrossedBenchmark
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RealSpaceIntegral
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.ExplicitMoments
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.GreenGeneratorMinors
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.MasslessX

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

/-- The physically normalized finite-regulator X conductivity, after
eliminating all three retarded/advanced Green Pauli minors in favor of
the **two common scalar Green generators and their first derivatives**.
This keeps the crossed-current Pauli channels, both Born impurity
correlators, the real-space Jacobian, and exactly the original
trace-only Bastin/current normalization.

This is an exact finite-momentum/finite-radius/finite-broadening
evaluation *boundary*. The final radial integral is not evaluated here. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_generator_radial_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .x e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
              v m probeEnergy broadening disorderStrength hbar pMax radius := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_eq_radial_antisymmetric_trace
    .x e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_generator_amplitude
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax]
  ring

/-- At *any finite regulator* the physically normalized Gaussian crossed
X Hall conductivity vanishes at zero Dirac mass, even for positive Born
scalar disorder strength. The proof uses the actual Born-Dyson effective
mass and two current-Pauli zero-mass selection rules, rather than the
weak-disorder closed Ado benchmark.

This exact massless statement is not an evaluation of the massive-metal
X integral or its ultraviolet/broadening limits. -/
@[simp] theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_zero_mass
    (e v probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
      .x e v 0 probeEnergy broadening disorderStrength hbar pMax rMax = 0 := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_generator_radial_integral
    e v 0 probeEnergy broadening disorderStrength hbar pMax rMax
    hhbar hbroadening hdisorder hpMax]
  have hzero (radius : ℝ) :
      finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
        v 0 probeEnergy broadening disorderStrength hbar pMax radius = 0 :=
    finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude_zero_mass
      v probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  simp_rw [hzero]
  simp

/-- The complete, physically normalized finite-regulator X Hall
conductivity is a radial integral depending on **one causal scalar
Born-Dyson Fourier generator and its real-space derivative**, together
with the explicitly retained effective spectral centers and crossed
current blocks. The advanced generator is its complex conjugate.

This is the precise real-space boundary immediately preceding any
Hankel/Bessel representation; neither the UV limit nor the radial
integral is evaluated. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_retardedGenerator_radial_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .x e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            finiteCutoffContinuumBornDysonGaussianCrossedXRetardedGeneratorRadialAmplitude
              v m probeEnergy broadening disorderStrength hbar pMax radius := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_generator_radial_integral
    e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hhbar hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude_eq_retarded
    v m probeEnergy broadening disorderStrength hbar pMax radius hbroadening]

/-- The regulated physical X Hall radial integrand is expressed solely in the
canonical K0/K1/K2 momentum moments, with the remaining retarded/advanced
Green scalar and z coefficients, transverse source-x current, and diagonal
source-y current all expanded. The signed Green radius and one Fourier
measure per real-space block remain explicit. No real-space integration or
regulator limit is asserted. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_x_eq_explicit_k0_k1_k2_moments_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .x e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (finiteCutoffContinuumBornDysonGaussianCrossedXFourierMomentKernel
              v m probeEnergy broadening disorderStrength hbar pMax radius) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_eq_radial_antisymmetric_trace
    .x e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_explicit_k0_k1_k2_moments
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  all_goals dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedXFourierMomentKernel, finiteCutoffContinuumBornDysonRadialPauliData]

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
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_eq_radial_antisymmetric_trace
    .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_real_minor
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]

/-- The finite-regulator physical Psi Hall integrand now contains only explicit
K0/K1/K2 radial momentum moments: the remaining retarded Green scalar/z
coefficients and source-x transverse current coefficient are expanded as well.
Each Fourier block retains its existing momentum measure. This is an exact
reduction, not a real-space radial evaluation or any regulator limit. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_psi_eq_explicit_k0_k1_k2_moments_integral
    (e v m probeEnergy broadening disorderStrength hbar pMax rMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity
        .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax =
      (((bastinStredaTraceConductivityPrefactor hbar * (e * v) ^ 2 : ℝ) : ℂ)) *
        (((disorderStrength ^ 2 : ℝ) : ℂ)) * (((2 * Real.pi : ℝ) : ℂ)) *
        ∫ radius in (0 : ℝ)..rMax,
          (radius : ℂ) *
            (finiteCutoffContinuumBornDysonGaussianCrossedPsiFourierMomentKernel
              v m probeEnergy broadening disorderStrength hbar pMax radius) := by
  rw [finiteCutoffContinuumBornDysonGaussianCrossedOrderedXYConductivity_eq_radial_antisymmetric_trace
    .psi e v m probeEnergy broadening disorderStrength hbar pMax rMax
    hbroadening hdisorder hpMax]
  congr 1
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only
  rw [finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_psi_antisymmetric_eq_explicit_k0_k1_k2_moments
    v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax]
  all_goals dsimp only [finiteCutoffContinuumBornDysonGaussianCrossedPsiFourierMomentKernel, finiteCutoffContinuumBornDysonRadialPauliData]

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

end

end QuantumTheory.Models.MassiveDirac
