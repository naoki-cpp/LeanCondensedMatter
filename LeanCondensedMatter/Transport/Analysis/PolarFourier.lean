import LeanCondensedMatter.Transport.Core.ContinuumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional polar Fourier transform

This module owns the representation-independent scalar Fourier transform used when a two-dimensional
physical-momentum integral is written in polar coordinates with a finite radial cutoff. The transform
includes the physical continuum normalization `d²p / (2πℏ)²` and the polar Jacobian `p`, while the
consumer supplies the momentum-space scalar field.

The full-angle kernels below are the canonical intermediate for radial Fourier reduction. They are
kept as explicit finite interval integrals rather than identified with Bessel functions here; the
pinned Mathlib revision does not yet provide its Bessel-function module. Model layers consume these
kernels without introducing a parallel special-function implementation.

No model Hamiltonian, matrix representation, disorder approximation, real-space cutoff, or
conductivity normalization is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- Two-dimensional polar point `(ρ cos φ, ρ sin φ)`. -/
def polarPoint2D (radius angle : ℝ) : Fin 2 → ℝ :=
  ![radius * Real.cos angle, radius * Real.sin angle]

/-- Fourier phase `exp(i p·r / ℏ)` for polar momentum `(p cos θ, p sin θ)` in two dimensions. -/
def physicalMomentumPolarFourierPhase
    (hbar p θ : ℝ) (r : Fin 2 → ℝ) : ℂ :=
  Complex.exp
    (Complex.I *
      (((p * (r 0 * Real.cos θ + r 1 * Real.sin θ) / hbar : ℝ) : ℂ)))

/-- Dimensionless radial phase `exp(i z cos θ)` that appears after aligning the real-space point with
the polar axis. -/
def polarFourierRadialPhase (z θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ)))

/-- The physical polar Fourier phase at a polar real-space point depends only on the angular
difference `θ - φ`. -/
theorem physicalMomentumPolarFourierPhase_polarPoint2D
    (hbar p θ radius angle : ℝ) :
    physicalMomentumPolarFourierPhase hbar p θ (polarPoint2D radius angle) =
      polarFourierRadialPhase (p * radius / hbar) (θ - angle) := by
  unfold physicalMomentumPolarFourierPhase polarFourierRadialPhase
  simp only [polarPoint2D, Matrix.cons_val_zero, Matrix.cons_val_one, Real.cos_sub]
  apply congrArg Complex.exp
  push_cast
  ring_nf

/-- Zeroth full-angle radial Fourier kernel. At a Mathlib revision with Bessel support this is the
integral representation that can be identified with `2π J₀(z)`. -/
noncomputable def polarFourierZerothAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase z θ

/-- First cosine full-angle radial Fourier kernel. At a Mathlib revision with Bessel support this is
the integral representation that can be identified with `2π i J₁(z)`. -/
noncomputable def polarFourierFirstCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)

/-- The sine first harmonic vanishes against the radial Fourier phase over one full angle. -/
theorem integral_polarFourierRadialPhase_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hneg :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    calc
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), -f θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            unfold f polarFourierRadialPhase
            rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
            push_cast
            ring
      _ = -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
        rw [intervalIntegral.integral_neg]
  have hself :
      -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ :=
    hneg.symm.trans hsub
  have hz : (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 :=
    CharZero.neg_eq_self_iff.mp hself
  simpa [f] using hz

/-- Full-angle reduction for a scalar field containing only constant and first sine/cosine
harmonics. The sine harmonic drops out on the radial axis, leaving the zeroth and first-cosine
kernels that later become the `J₀` and `J₁` channels. -/
theorem integral_polarFourierRadialPhase_first_harmonics
    (z p : ℝ) (a b c : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) *
        (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c)) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z * b) := by
  have hphase : Continuous fun θ : ℝ => polarFourierRadialPhase z θ := by
    unfold polarFourierRadialPhase
    fun_prop
  have hcos : Continuous fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) := by
    fun_prop
  have hsin : Continuous fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) := by
    fun_prop
  have hA : IntervalIntegrable
      (fun θ : ℝ => polarFourierRadialPhase z θ * a) volume 0 (2 * Real.pi) :=
    (hphase.mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hB : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) * b)
      volume 0 (2 * Real.pi) :=
    ((hphase.mul hcos).mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hC : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) * c)
      volume 0 (2 * Real.pi) :=
    ((hphase.mul hsin).mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z θ) *
          (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c)) =
        (p : ℂ) *
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
            polarFourierRadialPhase z θ * a +
              (polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) * b +
              (polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) * c := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro θ _
          ring
    _ = (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z * b) := by
      rw [intervalIntegral.integral_add (hA.add hB) hC,
        intervalIntegral.integral_add hA hB,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        integral_polarFourierRadialPhase_mul_sin_zero]
      simp [polarFourierZerothAngularKernel, polarFourierFirstCosineAngularKernel]

/-- Finite-cutoff polar Fourier transform of a complex scalar momentum field with the physical
momentum measure `d²p / (2πℏ)²` included exactly once. -/
noncomputable def finiteCutoffPhysicalMomentumPolarFourier
    (hbar pMax : ℝ) (field : ℝ → ℝ → ℂ) (r : Fin 2 → ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * physicalMomentumPolarFourierPhase hbar p θ r) * field p θ

/-- Radial-axis reduction of the finite-cutoff transform for a field with only constant and first
angular harmonics. The full angular integral is replaced exactly by the zeroth and first-cosine
radial kernels. -/
theorem finiteCutoffPhysicalMomentumPolarFourier_radialAxis_first_harmonics
    (hbar pMax radius : ℝ) (a b c : ℝ → ℂ) :
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
        (fun p θ =>
          a p + ((Real.cos θ : ℝ) : ℂ) * b p + ((Real.sin θ : ℝ) : ℂ) * c p)
        (polarPoint2D radius 0) =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) *
            (polarFourierZerothAngularKernel (p * radius / hbar) * a p +
              polarFourierFirstCosineAngularKernel (p * radius / hbar) * b p) := by
  unfold finiteCutoffPhysicalMomentumPolarFourier
  apply congrArg (((momentumMeasurePrefactor hbar : ℝ) : ℂ) * ·)
  apply intervalIntegral.integral_congr
  intro p _
  simp_rw [physicalMomentumPolarFourierPhase_polarPoint2D]
  simp only [sub_zero]
  exact integral_polarFourierRadialPhase_first_harmonics
    (p * radius / hbar) p (a p) (b p) (c p)

end

end Transport
end QuantumTheory
