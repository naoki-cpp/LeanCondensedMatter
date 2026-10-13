import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator

set_option linter.style.header false

/-!
# Radial finite-cutoff Born-Dyson Green matrix

This module owns the one-dimensional real-space radial Green kernels and their
entrywise and Pauli-coefficient momentum integrals. It proves finite-regulator
continuity and interval integrability, then the exact inversion law under
reversing the signed radial real-space coordinate.

The physical momentum measure and zeroth/first polar Fourier kernels remain
explicit. The two-dimensional real-space Green matrix and its polar-angle
reduction are downstream in `FiniteBroadeningBornRealSpacePropagator`.
No angular integration beyond these kernels or cutoff/broadening limit is taken.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

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
    unfold finiteCutoffContinuumBornDysonRadialGreenEntryKernel <;>
    dsimp <;>
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

end QuantumTheory.Models.MassiveDirac
