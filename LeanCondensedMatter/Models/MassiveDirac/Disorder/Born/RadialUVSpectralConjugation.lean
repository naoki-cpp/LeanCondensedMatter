import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVSpectralCenter
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Causal complex conjugation of the fixed-spectral Fourier UV boundary

The universal 2D Dirac scalar radial Fourier ultraviolet boundary
obeys the exact adjointness/conjugation rule at nonreal spectral
center. Crucially, this is proved as a limit of the *finite-cutoff*
Fourier integrals, using their real K0 angular kernel, rather than
postulating Hankel branch relations.

In the retarded/advanced application this identifies the two causal
ultraviolet values and fixes the orientation of the eventual Bessel
Y or Hankel branch choice. No fixed- or running-Born spectral limit
is silently inserted.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval ComplexConjugate

/-- The quadratic massive-Dirac radial denominator conjugates by
conjugating its two complex spectral parameters. -/
theorem massiveDiracRadialDenominator_conj
    (v p : ℝ) (energy mass : ℂ) :
    conj (massiveDiracRadialDenominator v p energy mass) =
      massiveDiracRadialDenominator v p (conj energy) (conj mass) := by
  simp [massiveDiracRadialDenominator, map_sub, map_pow, Complex.conj_ofReal]

/-- Complex conjugation commutes with each finite radial Fourier
integral at a fixed complex spectral center. -/
theorem integral_massiveDiracRadialFourier_conj
    (v c b : ℝ) (energy mass : ℂ) :
    conj (∫ p in (0 : ℝ)..b,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
        (massiveDiracRadialDenominator v p energy mass)⁻¹) =
      ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p (conj energy) (conj mass))⁻¹ := by
  have hmove :
      conj (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹) =
        ∫ p in (0 : ℝ)..b,
          conj ((p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹) := by
    simpa using
      ((Complex.conjLIE.toLinearIsometry).intervalIntegral_comp_comm
        (f := fun p : ℝ =>
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹)
        (a := (0 : ℝ)) (b := b)).symm
  rw [hmove]
  apply intervalIntegral.integral_congr
  intro p _
  simp only [map_mul, Complex.conj_inv, Complex.conj_ofReal,
    polarFourierZerothAngularKernel_conj]
  rw [massiveDiracRadialDenominator_conj]

/-- The canonical Fourier UV Green function commutes with complex
conjugation of its fixed energy and mass arguments, at a nonreal
quadratic spectral center. The proof uses actual cutoff-integral
conjugation and uniqueness of the previously proved limits. -/
theorem massiveDiracRadialFourierUVValue_conj
    (v c : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    conj (massiveDiracRadialFourierUVValue v c energy mass) =
      massiveDiracRadialFourierUVValue v c (conj energy) (conj mass) := by
  have hcenterStar :
      ((conj energy) ^ 2 - (conj mass) ^ 2).im ≠ 0 := by
    have hstar :
        (conj energy) ^ 2 - (conj mass) ^ 2 =
          conj (energy ^ 2 - mass ^ 2) := by
      simp only [map_pow, map_sub]
    rw [hstar, Complex.conj_im]
    exact neg_ne_zero.mpr hcenter
  have hret := massiveDiracRadialFourier_tendsto_uvValue
    v c energy mass hv hc hcenter
  have hadv := massiveDiracRadialFourier_tendsto_uvValue
    v c (conj energy) (conj mass) hv hc hcenterStar
  have hconj :
      Filter.Tendsto (fun b : ℝ =>
        conj (∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹))
        Filter.atTop
        (nhds (conj (massiveDiracRadialFourierUVValue v c energy mass))) :=
    (Complex.continuous_conj.tendsto _).comp hret
  have hpoint (b : ℝ) :
      conj (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹) =
        ∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p (conj energy) (conj mass))⁻¹ :=
    integral_massiveDiracRadialFourier_conj v c b energy mass
  exact tendsto_nhds_unique
    (hconj.congr' (Filter.Eventually.of_forall fun b => (hpoint b).symm))
    hadv

/-- The center-only canonical function has the natural conjugation
symmetry under Z -> conj Z, without choosing a square-root branch. -/
theorem massiveDiracRadialFourierUVCenter_conj
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    conj (massiveDiracRadialFourierUVCenter v c center) =
      massiveDiracRadialFourierUVCenter v c (conj center) := by
  let energy : ℂ := Complex.sqrt center
  have hcenterEq : energy ^ 2 - (0 : ℂ) ^ 2 = center := by
    simp [energy, complex_sqrt_sq_spectral_center]
  have hconjEq :
      (conj energy) ^ 2 - (conj (0 : ℂ)) ^ 2 = conj center := by
    simpa only [map_sub, map_pow] using (congrArg conj hcenterEq)
  have h := massiveDiracRadialFourierUVValue_conj
    v c energy 0 hv hc (by simpa [hcenterEq] using hcenter)
  rw [massiveDiracRadialFourierUVValue_eq_center,
    massiveDiracRadialFourierUVValue_eq_center, hcenterEq, hconjEq] at h
  exact h

end

end QuantumTheory.Models.MassiveDirac
