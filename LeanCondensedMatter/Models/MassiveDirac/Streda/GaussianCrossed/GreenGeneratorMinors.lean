import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialConjugation
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RealSpaceIntegral
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Generator factorization of the finite-regulator crossed X Green minors

The Gaussian crossed X trace contains three antisymmetric products of
retarded/advanced Green Pauli channels. Their existing K0/K1 moment
representations involve several individually regulated Fourier integrals.

At any finite momentum cutoff and nonzero external broadening, the scalar
and Pauli-z Green components are respectively the effective energy and
mass times one common scalar resolvent generator `F_s(r)`. The Pauli-x
component is `-i ℏ v F_s'(r)`. These *proved* finite-cutoff identities
give exact factorized expressions for all three Green minors of the X
Hall integrand, with the sign and order of the R/A factors preserved.

No second-kind Bessel function, infinite-cutoff limit, radial X
integration, or closed crossed Hall conductivity is assumed.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

/-- The three retarded/advanced Green Pauli minors appearing in the finite-radius
X topology all depend on only two scalar Fourier generators and their radial
derivatives.

The first line eliminates four separate K0 Green moments in favor of
`(E_R M_A - E_A M_R) F_R F_A`. The other two lines isolate precisely the
two first-order radial derivative structures required to integrate the
X trace. The third minor has the A-scalar/R-x ordering of the physical
X Hall integrand, not the opposite sign.

At fixed nonzero `ℏ`, broadening, and nonnegative disorder/cutoff
these are algebraic consequences of the actual Born-Dyson propagator. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedXGreenMinors_eq_generators
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    let eR := finiteCutoffContinuumBornEffectiveEnergy
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let eA := finiteCutoffContinuumBornEffectiveEnergy
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let mR := finiteCutoffContinuumBornEffectiveMass
      .retarded v m probeEnergy broadening disorderStrength hbar pMax
    let mA := finiteCutoffContinuumBornEffectiveMass
      .advanced v m probeEnergy broadening disorderStrength hbar pMax
    let fR := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    let fA := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    let dfR := deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .retarded v m probeEnergy broadening disorderStrength hbar pMax r) radius
    let dfA := deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .advanced v m probeEnergy broadening disorderStrength hbar pMax r) radius
    let sR := finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    let sA := finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    let zR := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .z
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    let zA := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .z
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    let xR := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .x
      .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    let xA := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient .x
      .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    (sR * zA - sA * zR =
      (eR * mA - eA * mR) * fR * fA) ∧
    (xR * zA - zR * xA =
      (-Complex.I * (((hbar * v : ℝ) : ℂ))) *
        (mA * dfR * fA - mR * fR * dfA)) ∧
    (sA * xR - sR * xA =
      (-Complex.I * (((hbar * v : ℝ) : ℂ))) *
        (eA * fA * dfR - eR * fR * dfA)) := by
  dsimp only
  have hsR := finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_generator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  have hsA := finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_generator
    .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  have hzR := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_z_eq_generator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  have hzA := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_z_eq_generator
    .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax
  have hxR := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_eq_deriv_generator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax
  have hxA := finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_x_eq_deriv_generator
    .advanced v m probeEnergy broadening disorderStrength hbar pMax radius
    hhbar hbroadening hdisorder hpMax
  rw [hsR, hsA, hzR, hzA, hxR, hxA]
  constructor
  · ring
  constructor <;> ring


/-- The exact radial Pauli trace amplitude used for the finite-cutoff X
Hall integral, with *every Green minor* reduced to the scalar
generators `F_R,F_A` and their first real-space derivatives.

Current-source Pauli coefficients remain the physical, finite-cutoff
Gaussian-crossed current blocks; no independent scalar/current model
is introduced. In particular, the retarded/advanced Green arguments
are `-radius`, as required by the original X topology. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
    0 v m probeEnergy broadening disorderStrength hbar pMax radius
  let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
    1 v m probeEnergy broadening disorderStrength hbar pMax radius
  let a := InternalSpace.pauliScalarCoefficient Jx
  let c := InternalSpace.pauliScalarCoefficient Jy
  let u := InternalSpace.pauliVectorCoefficient Jx
  let w := InternalSpace.pauliVectorCoefficient Jy
  let eR := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let eA := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let mR := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let mA := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let fR := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
  let fA := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    .advanced v m probeEnergy broadening disorderStrength hbar pMax (-radius)
  let dfR := deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax r) (-radius)
  let dfA := deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    .advanced v m probeEnergy broadening disorderStrength hbar pMax r) (-radius)
  2 * Complex.I *
    ((a * w .y - c * u .y) *
        ((-Complex.I * (((hbar * v : ℝ) : ℂ))) *
          (mA * dfR * fA - mR * fR * dfA)) +
      ((eR * mA - eA * mR) * fR * fA) *
        (w .y * u .x + (u .y) ^ 2) +
      ((-Complex.I * (((hbar * v : ℝ) : ℂ))) *
        (eA * fA * dfR - eR * fR * dfA)) *
        (w .y * u .z - u .y * w .z))

/-- Finite-regulator X radial antisymmetric source trace in terms of
two scalar Green generators and their derivatives, with all current
Pauli coefficients unchanged. The equality is *pointwise in radius*
and precedes the real-space integration. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_generator_amplitude
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hhbar : hbar ≠ 0)
    (hbroadening : broadening ≠ 0)
    (hdisorder : 0 ≤ disorderStrength) (hpMax : 0 ≤ pMax) :
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor .x
        v m probeEnergy broadening disorderStrength hbar pMax radius 0 1 -
      finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor .x
        v m probeEnergy broadening disorderStrength hbar pMax radius 1 0 =
      2 * finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
        v m probeEnergy broadening disorderStrength hbar pMax radius := by
  have htrace :=
    finiteCutoffContinuumBornDysonGaussianCrossedRadialTraceTensor_x_antisymmetric_eq_transverse_minors
      v m probeEnergy broadening disorderStrength hbar pMax radius
      hbroadening hdisorder hpMax
  obtain ⟨hscalarZ, hxZ, hscalarX⟩ :=
    finiteCutoffContinuumBornDysonGaussianCrossedXGreenMinors_eq_generators
      v m probeEnergy broadening disorderStrength hbar pMax (-radius)
      hhbar hbroadening hdisorder hpMax
  dsimp only at htrace hscalarZ hxZ hscalarX
  rw [htrace]
  unfold finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
  dsimp only
  simp only [finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient] at hscalarZ hxZ hscalarX
  rw [hscalarZ, hxZ, hscalarX]
  ring


/-- Single-causal-branch presentation of the *physical regulated X radial
amplitude*. The advanced scalar Green Fourier generator and its derivative
are replaced by conjugates of the retarded ones at the same -radius.

This retains the finite Born-Dyson current block, both effective R/A
spectral centers, the original crossed trace normalization, and finite
momentum/real-space cutoffs. It does not assume an infinite-cutoff
Hankel formula or evaluate the last radial integral. -/
noncomputable def finiteCutoffContinuumBornDysonGaussianCrossedXRetardedGeneratorRadialAmplitude
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  let Jx := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
    0 v m probeEnergy broadening disorderStrength hbar pMax radius
  let Jy := finiteCutoffContinuumBornDysonGaussianCrossedRadialRealSpaceCurrentBlock
    1 v m probeEnergy broadening disorderStrength hbar pMax radius
  let a := InternalSpace.pauliScalarCoefficient Jx
  let c := InternalSpace.pauliScalarCoefficient Jy
  let u := InternalSpace.pauliVectorCoefficient Jx
  let w := InternalSpace.pauliVectorCoefficient Jy
  let eR := finiteCutoffContinuumBornEffectiveEnergy
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let eA := finiteCutoffContinuumBornEffectiveEnergy
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let mR := finiteCutoffContinuumBornEffectiveMass
    .retarded v m probeEnergy broadening disorderStrength hbar pMax
  let mA := finiteCutoffContinuumBornEffectiveMass
    .advanced v m probeEnergy broadening disorderStrength hbar pMax
  let fR := finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius)
  let fA := conj (finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax (-radius))
  let dfR := deriv (fun r : ℝ => finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
    .retarded v m probeEnergy broadening disorderStrength hbar pMax r) (-radius)
  let dfA := conj (deriv (fun r : ℝ =>
    finiteCutoffContinuumBornDysonRadialScalarGreenGenerator
      .retarded v m probeEnergy broadening disorderStrength hbar pMax r) (-radius))
  2 * Complex.I *
    ((a * w .y - c * u .y) *
        ((-Complex.I * (((hbar * v : ℝ) : ℂ))) *
          (mA * dfR * fA - mR * fR * dfA)) +
      ((eR * mA - eA * mR) * fR * fA) *
        (w .y * u .x + (u .y) ^ 2) +
      ((-Complex.I * (((hbar * v : ℝ) : ℂ))) *
        (eA * fA * dfR - eR * fR * dfA)) *
        (w .y * u .z - u .y * w .z))

/-- Exact equality of the X generator amplitude and the
single-causal-branch expression. The reduction relies only on the
physical finite-cutoff denominator's retarded/advanced adjointness. -/
theorem finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude_eq_retarded
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) :
    finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
      v m probeEnergy broadening disorderStrength hbar pMax radius =
    finiteCutoffContinuumBornDysonGaussianCrossedXRetardedGeneratorRadialAmplitude
      v m probeEnergy broadening disorderStrength hbar pMax radius := by
  unfold finiteCutoffContinuumBornDysonGaussianCrossedXGeneratorRadialAmplitude
    finiteCutoffContinuumBornDysonGaussianCrossedXRetardedGeneratorRadialAmplitude
  dsimp only
  rw [finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_conj
    v m probeEnergy broadening disorderStrength hbar pMax (-radius) hbroadening,
    ← finiteCutoffContinuumBornDysonRadialScalarGreenGenerator_deriv_conj
      v m probeEnergy broadening disorderStrength hbar pMax (-radius) hbroadening]

end

end QuantumTheory.Models.MassiveDirac
