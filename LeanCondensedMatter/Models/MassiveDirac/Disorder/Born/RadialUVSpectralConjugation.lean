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

/-- Each finite-cutoff Fourier integral conjugates under conjugation
of its quadratic spectral center. -/
private theorem integral_massiveDiracRadialFourierCenter_conj
    (v c b : ℝ) (center : ℂ) :
    conj (∫ p in (0 : ℝ)..b,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
        (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) =
      ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (conj center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹ := by
  have hmove :
      conj (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) =
        ∫ p in (0 : ℝ)..b,
          conj ((p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) := by
    simpa using
      ((Complex.conjLIE.toLinearIsometry).intervalIntegral_comp_comm
        (f := fun p : ℝ =>
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹)
        (a := (0 : ℝ)) (b := b)).symm
  rw [hmove]
  apply intervalIntegral.integral_congr
  intro p _
  simp only [map_mul, Complex.conj_inv, Complex.conj_ofReal,
    polarFourierZerothAngularKernel_conj, map_sub]

/-- The center-only UV value conjugates under Z ↦ conj Z, using
the symmetry of its finite-cutoff Fourier integrals. -/
theorem massiveDiracRadialFourierUVCenter_conj
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    conj (massiveDiracRadialFourierUVCenter v c center) =
      massiveDiracRadialFourierUVCenter v c (conj center) := by
  have hcenterStar : (conj center).im ≠ 0 := by
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr hcenter
  have hret := massiveDiracRadialFourier_tendsto_uvValue_center
    v c center hv hc hcenter
  have hadv := massiveDiracRadialFourier_tendsto_uvValue_center
    v c (conj center) hv hc hcenterStar
  have hconj :
      Filter.Tendsto (fun b : ℝ =>
        conj (∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹))
        Filter.atTop
        (nhds (conj (massiveDiracRadialFourierUVCenter v c center))) :=
    (Complex.continuous_conj.tendsto _).comp hret
  have hpoint (b : ℝ) :
      conj (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) =
        ∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (conj center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹ :=
    integral_massiveDiracRadialFourierCenter_conj v c b center
  exact tendsto_nhds_unique
    (hconj.congr' (Filter.Eventually.of_forall hpoint))
    hadv

end

end QuantumTheory.Models.MassiveDirac
