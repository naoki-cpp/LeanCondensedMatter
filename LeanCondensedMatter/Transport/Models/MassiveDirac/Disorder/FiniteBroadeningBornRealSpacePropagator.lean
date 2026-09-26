import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator

set_option linter.style.header false

/-!
# Finite-cutoff real-space Born-Dyson propagator

This module owns the real-space representation of the finite-cutoff finite-broadening Born-Dyson
Green matrix. The matrix Fourier transform is performed entrywise through the generic two-dimensional
physical-momentum polar Fourier transform, so the factor `d²p / (2πℏ)²` is already included in every
real-space Green block.

The generic Fourier reduction uses the model-independent constant/first/second harmonic kernels from
`Transport.Analysis.PolarFourier` at an arbitrary polar point. On the positive real-space radial axis,
the massive-Dirac Green matrix has vanishing second-harmonic coefficients and the first-sine channel
is suppressed by the point angle, leaving the zeroth and first-cosine kernels. The Green matrix
supplies one `AngularHarmonicCoefficients` value at each radial momentum; entrywise Fourier reduction
consumes that common decomposition without rebuilding angular integrability.

No crossed-diagram topology, current vertex, real-space integration, cutoff removal, or conductivity
normalization is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Finite-cutoff finite-`η` real-space Born-Dyson Green matrix. -/
noncomputable def finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : Matrix2 :=
  fun i j =>
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
      (fun p θ =>
        finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax i j)
      r

/-- At finite broadening, the radial Born-Dyson scalar coefficient is continuous in radial
momentum. -/
theorem continuous_finiteCutoffContinuumBornDysonScalarCoefficient_radial
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    Continuous fun p : ℝ =>
      finiteCutoffContinuumBornDysonScalarCoefficient
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  have hden : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax ≠ 0 := by
    intro p
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hdenContinuous : Continuous fun p : ℝ =>
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonDenominator
    fun_prop
  unfold finiteCutoffContinuumBornDysonScalarCoefficient
  exact (hdenContinuous.inv₀ hden).mul continuous_const

/-- At finite broadening, every radial Born-Dyson Pauli coefficient is continuous in radial
momentum. -/
theorem continuous_finiteCutoffContinuumBornDysonPauliCoefficient_radial
    (axis : PauliAxis) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    Continuous fun p : ℝ =>
      finiteCutoffContinuumBornDysonPauliCoefficient
        axis side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
  have hden : ∀ p : ℝ,
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax ≠ 0 := by
    intro p
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hdenContinuous : Continuous fun p : ℝ =>
      finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonDenominator
    fun_prop
  have hinv : Continuous fun p : ℝ =>
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ :=
    hdenContinuous.inv₀ hden
  unfold finiteCutoffContinuumBornDysonPauliCoefficient
  cases axis <;>
    simp only [InternalSpace.pauliAxisComponent] <;>
    fun_prop

/-- Scalar radial momentum kernel for one finite-cutoff Born-Dyson Green-matrix entry. The
physical momentum-measure prefactor remains outside the one-dimensional integral. -/
noncomputable def finiteCutoffContinuumBornDysonRadialGreenEntryKernel
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (i j : Fin 2) : ℂ :=
  let a := finiteCutoffContinuumBornDysonScalarCoefficient
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let k0 := polarFourierZerothAngularKernel (p * radius / hbar)
  let k1 := polarFourierFirstCosineAngularKernel (p * radius / hbar)
  (p : ℂ) *
    (!![k0 * (a + d), k1 * b;
        k1 * b, k0 * (a - d)] : Matrix2) i j

/-- In the finite-broadening finite-cutoff regime, every radial Green entry kernel is
continuous in radial momentum. -/
theorem continuous_finiteCutoffContinuumBornDysonRadialGreenEntryKernel
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) (i j : Fin 2) :
    Continuous fun p : ℝ =>
      finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j := by
  have ha :=
    continuous_finiteCutoffContinuumBornDysonScalarCoefficient_radial
      side v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hb :=
    continuous_finiteCutoffContinuumBornDysonPauliCoefficient_radial
      .x side v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have hd :=
    continuous_finiteCutoffContinuumBornDysonPauliCoefficient_radial
      .z side v m probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  fin_cases i <;> fin_cases j <;>
    simp [finiteCutoffContinuumBornDysonRadialGreenEntryKernel] <;>
    fun_prop

/-- In the finite-broadening finite-cutoff regime, every radial Green entry kernel is interval
integrable on the regulated radial momentum interval. -/
theorem intervalIntegrable_finiteCutoffContinuumBornDysonRadialGreenEntryKernel
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) (i j : Fin 2) :
    IntervalIntegrable
      (fun p : ℝ => finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p i j)
      MeasureTheory.volume 0 pMax :=
  (continuous_finiteCutoffContinuumBornDysonRadialGreenEntryKernel
    side v m probeEnergy broadening disorderStrength hbar pMax radius
    hbroadening hdisorder hpMax i j).intervalIntegrable 0 pMax

/-- One-dimensional radial-kernel representation of the finite-cutoff Born-Dyson Green matrix on
the positive real-space radial axis. The diagonal channels carry the zeroth angular kernel, while
the off-diagonal in-plane channel carries the first-cosine kernel. -/
noncomputable def finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : Matrix2 :=
  let a : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let prefactor : ℂ := ((momentumMeasurePrefactor hbar : ℝ) : ℂ)
  let k0 : ℝ → ℂ := fun p =>
    polarFourierZerothAngularKernel (p * radius / hbar)
  let k1 : ℝ → ℂ := fun p =>
    polarFourierFirstCosineAngularKernel (p * radius / hbar)
  !![
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k0 p * (a p + d p)),
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k1 p * b p);
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k1 p * b p),
    prefactor * ∫ p in (0 : ℝ)..pMax, (p : ℂ) * (k0 p * (a p - d p))]

/-- Scalar Pauli coefficient of the positive-axis radial Born-Dyson Green matrix. -/
noncomputable def finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  InternalSpace.pauliScalarCoefficient
    (finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      side v m probeEnergy broadening disorderStrength hbar pMax radius)

/-- Axis-indexed Pauli coefficient of the positive-axis radial Born-Dyson Green matrix. -/
noncomputable def finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
    (axis : PauliAxis) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) : ℂ :=
  InternalSpace.pauliVectorCoefficient
    (finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
      side v m probeEnergy broadening disorderStrength hbar pMax radius) axis

/-- Pointwise scalar Pauli kernel of the positive-axis radial Born-Dyson Green integrand. -/
noncomputable def finiteCutoffContinuumBornDysonRadialGreenScalarKernel
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) : ℂ :=
  let a := finiteCutoffContinuumBornDysonScalarCoefficient
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let k0 := polarFourierZerothAngularKernel (p * radius / hbar)
  (p : ℂ) * (k0 * a)

/-- Pointwise Pauli-vector kernel of the positive-axis radial Born-Dyson Green integrand. -/
noncomputable def finiteCutoffContinuumBornDysonRadialGreenPauliKernel
    (axis : PauliAxis) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) : ℂ :=
  let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let k0 := polarFourierZerothAngularKernel (p * radius / hbar)
  let k1 := polarFourierFirstCosineAngularKernel (p * radius / hbar)
  match axis with
  | .x => (p : ℂ) * (k1 * b)
  | .y => 0
  | .z => (p : ℂ) * (k0 * d)

/-- The pointwise radial Green entry kernel has exactly the scalar coefficient carried by the
zeroth angular Fourier channel. -/
theorem finiteCutoffContinuumBornDysonRadialGreenEntryKernel_pauliScalarCoefficient
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) :
    InternalSpace.pauliScalarCoefficient
        (fun i j =>
          finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius p i j) =
      finiteCutoffContinuumBornDysonRadialGreenScalarKernel
        side v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  simp [InternalSpace.pauliScalarCoefficient,
    finiteCutoffContinuumBornDysonRadialGreenEntryKernel,
    finiteCutoffContinuumBornDysonRadialGreenScalarKernel]
  ring

/-- The pointwise radial Green entry kernel carries the first angular Fourier channel in the
in-plane x component, no y component on the radial axis, and the zeroth channel in z. -/
theorem finiteCutoffContinuumBornDysonRadialGreenEntryKernel_pauliVectorCoefficient
    (axis : PauliAxis) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) :
    InternalSpace.pauliVectorCoefficient
        (fun i j =>
          finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius p i j) axis =
      finiteCutoffContinuumBornDysonRadialGreenPauliKernel
        axis side v m probeEnergy broadening disorderStrength hbar pMax radius p := by
  cases axis <;>
    simp [InternalSpace.pauliVectorCoefficient,
      finiteCutoffContinuumBornDysonRadialGreenEntryKernel,
      finiteCutoffContinuumBornDysonRadialGreenPauliKernel]
  all_goals ring

/-- Each entry of the radial Born-Dyson Green matrix is the physical momentum-measure prefactor
times the integral of its scalar radial kernel. -/
theorem finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (i j : Fin 2) :
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax radius i j =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          finiteCutoffContinuumBornDysonRadialGreenEntryKernel
            side v m probeEnergy broadening disorderStrength hbar pMax radius p i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The scalar Pauli coefficient of the radial Green matrix is a combination of its two
scalar entry-kernel integrals; no matrix operation remains on the right-hand side. -/
theorem finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient_eq_entryKernel_integrals
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
        side v m probeEnergy broadening disorderStrength hbar pMax radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
          (∫ p in (0 : ℝ)..pMax,
            finiteCutoffContinuumBornDysonRadialGreenEntryKernel
              side v m probeEnergy broadening disorderStrength hbar pMax radius p 0 0) +
        ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
          (∫ p in (0 : ℝ)..pMax,
            finiteCutoffContinuumBornDysonRadialGreenEntryKernel
              side v m probeEnergy broadening disorderStrength hbar pMax radius p 1 1)) / 2 := by
  unfold finiteCutoffContinuumBornDysonRadialGreenScalarCoefficient
  rw [InternalSpace.pauliScalarCoefficient]
  rw [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral,
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral]

/-- Each Pauli-vector component of the radial Green matrix is a scalar combination of entry-kernel
integrals. This is the matrix-free boundary consumed by crossed radial traces. -/
theorem finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient_eq_entryKernel_integrals
    (axis : PauliAxis) (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
        axis side v m probeEnergy broadening disorderStrength hbar pMax radius =
      match axis with
      | .x =>
          (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                  side v m probeEnergy broadening disorderStrength hbar pMax radius p 0 1) +
            ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                  side v m probeEnergy broadening disorderStrength hbar pMax radius p 1 0)) / 2
      | .y =>
          Complex.I *
            (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
                (∫ p in (0 : ℝ)..pMax,
                  finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                    side v m probeEnergy broadening disorderStrength hbar pMax radius p 0 1) -
              ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
                (∫ p in (0 : ℝ)..pMax,
                  finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                    side v m probeEnergy broadening disorderStrength hbar pMax radius p 1 0)) / 2
      | .z =>
          (((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                  side v m probeEnergy broadening disorderStrength hbar pMax radius p 0 0) -
            ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
              (∫ p in (0 : ℝ)..pMax,
                finiteCutoffContinuumBornDysonRadialGreenEntryKernel
                  side v m probeEnergy broadening disorderStrength hbar pMax radius p 1 1)) / 2 := by
  unfold finiteCutoffContinuumBornDysonRadialGreenPauliCoefficient
  cases axis <;>
    simp only [InternalSpace.pauliVectorCoefficient] <;>
    rw [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral,
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral]

/-- The two-dimensional polar Fourier representation of the finite-cutoff Born-Dyson Green matrix
reduces exactly to the one-dimensional zeroth/first angular kernels on the positive real-space
radial axis. -/
theorem finiteCutoffContinuumBornDysonRealSpaceGreenMatrix_radialAxis_eq
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax
        (polarPoint2D radius 0) =
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax radius := by
  let a : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonScalarCoefficient
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .x
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d : ℝ → ℂ := fun p =>
    finiteCutoffContinuumBornDysonPauliCoefficient .z
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let harmonics : ℝ → AngularHarmonicCoefficients Matrix2 := fun p =>
    { constant := a p • (1 : Matrix2) + d p • sigmaZ
      firstCosine := b p • sigmaX
      firstSine := b p • sigmaY
      secondCosine := 0
      secondMixed := 0 }
  let entryHarmonics : Fin 2 → Fin 2 → ℝ → AngularHarmonicCoefficients ℂ :=
    fun i j p =>
      { constant := (harmonics p).constant i j
        firstCosine := (harmonics p).firstCosine i j
        firstSine := (harmonics p).firstSine i j
        secondCosine := (harmonics p).secondCosine i j
        secondMixed := (harmonics p).secondMixed i j }
  have hpolar (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        polarPauliMatrix (a p) (b p) (d p) θ := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [finiteCutoffContinuumBornDysonGreenOperator, polarPauliOperator,
      matrixOperator, a, b, d] using
      (finiteCutoffContinuumBornDysonGreenOperator_polar_eq
        side v m p θ probeEnergy broadening disorderStrength hbar pMax)
  have hfield (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        (harmonics p).eval θ := by
    rw [hpolar]
    simp [harmonics, AngularHarmonicCoefficients.eval, polarPauliMatrix]
    module
  have hentry (i j : Fin 2) (p θ : ℝ) :
      finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax i j =
        (entryHarmonics i j p).eval θ := by
    have h := congrArg (fun M : Matrix2 => M i j) (hfield p θ)
    simpa [entryHarmonics, AngularHarmonicCoefficients.eval, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul] using h
  funext i j
  fin_cases i <;> fin_cases j
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 0 0)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 0 0]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 0 0))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 0 1)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 0 1]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 0 1))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 1 0)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 1 0]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, InternalSpace.pauliX, InternalSpace.pauliY,
      InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 1 0))
  · change
      finiteCutoffPhysicalMomentumPolarFourier hbar pMax
          (fun p θ =>
            finiteCutoffContinuumBornDysonGreenMatrix
              side v m (p * Real.cos θ) (p * Real.sin θ)
              probeEnergy broadening disorderStrength hbar pMax 1 1)
          (polarPoint2D radius 0) = _
    simp_rw [hentry 1 1]
    simpa [finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix,
      entryHarmonics, harmonics, a, b, d, sub_eq_add_neg, InternalSpace.pauliX,
      InternalSpace.pauliY, InternalSpace.pauliZ] using
      (finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
        hbar pMax radius 0 (entryHarmonics 1 1))


private theorem finiteCutoffContinuumBornDysonRadialGreenEntryKernel_neg_radius
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ)
    (i j : Fin 2) :
    finiteCutoffContinuumBornDysonRadialGreenEntryKernel
        side v m probeEnergy broadening disorderStrength hbar pMax (-radius) p i j =
      sigmaZ i i *
        finiteCutoffContinuumBornDysonRadialGreenEntryKernel
          side v m probeEnergy broadening disorderStrength hbar pMax radius p i j *
        sigmaZ j j := by
  let a := finiteCutoffContinuumBornDysonScalarCoefficient
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let b := finiteCutoffContinuumBornDysonPauliCoefficient .x
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  let d := finiteCutoffContinuumBornDysonPauliCoefficient .z
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  have harg : p * (-radius) / hbar = -(p * radius / hbar) := by
    ring
  fin_cases i <;> fin_cases j
  · change
      (p : ℂ) *
          (polarFourierZerothAngularKernel (p * (-radius) / hbar) * (a + d)) =
        sigmaZ 0 0 *
            ((p : ℂ) *
              (polarFourierZerothAngularKernel (p * radius / hbar) * (a + d))) *
          sigmaZ 0 0
    rw [harg, polarFourierZerothAngularKernel_neg]
    simp [sigmaZ, InternalSpace.pauliZ]
  · change
      (p : ℂ) *
          (polarFourierFirstCosineAngularKernel (p * (-radius) / hbar) * b) =
        sigmaZ 0 0 *
            ((p : ℂ) *
              (polarFourierFirstCosineAngularKernel (p * radius / hbar) * b)) *
          sigmaZ 1 1
    rw [harg, polarFourierFirstCosineAngularKernel_neg]
    simp [sigmaZ, InternalSpace.pauliZ]
  · change
      (p : ℂ) *
          (polarFourierFirstCosineAngularKernel (p * (-radius) / hbar) * b) =
        sigmaZ 1 1 *
            ((p : ℂ) *
              (polarFourierFirstCosineAngularKernel (p * radius / hbar) * b)) *
          sigmaZ 0 0
    rw [harg, polarFourierFirstCosineAngularKernel_neg]
    simp [sigmaZ, InternalSpace.pauliZ]
  · change
      (p : ℂ) *
          (polarFourierZerothAngularKernel (p * (-radius) / hbar) * (a - d)) =
        sigmaZ 1 1 *
            ((p : ℂ) *
              (polarFourierZerothAngularKernel (p * radius / hbar) * (a - d))) *
          sigmaZ 1 1
    rw [harg, polarFourierZerothAngularKernel_neg]
    simp [sigmaZ, InternalSpace.pauliZ]

/-- Reversing the radial real-space coordinate conjugates the massive-Dirac Green matrix by
`σ_z`. The diagonal zeroth-harmonic channels are even, while the off-diagonal first-harmonic
channel is odd. -/
@[simp] theorem finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_neg_radius
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
        side v m probeEnergy broadening disorderStrength hbar pMax (-radius) =
      sigmaZ *
        finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix
          side v m probeEnergy broadening disorderStrength hbar pMax radius *
        sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, InternalSpace.pauliZ, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two,
      finiteCutoffContinuumBornDysonRadialRealSpaceGreenMatrix_apply_eq_entryKernel_integral,
      finiteCutoffContinuumBornDysonRadialGreenEntryKernel_neg_radius]


end

end QuantumTheory.Transport.Models.MassiveDirac
