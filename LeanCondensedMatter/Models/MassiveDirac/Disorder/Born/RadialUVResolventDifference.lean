import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBesselJ
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Resolvent difference of the unit-velocity Fourier UV Green function

The key Fourier–Hankel integral for a single spectral center converges
only *oscillatorily*. Taking a difference of two nonreal spectral centers
cancels its leading large-momentum `p⁻²` behavior. The resulting
two-resolvent integrand behaves as `p⁻³` after the radial measure
and is **absolutely integrable**. That analytic improvement is the
route to a normalized Stieltjes-transform proof of the outstanding
upper-half-plane Fourier–Hankel identity.

Here we prove the exact two-resolvent identity at every finite cutoff
and transport it through the existing proven UV limits. The
absolute-integrability theorem is a separate next step, not silently
inferred from pointwise asymptotics. No Hankel evaluation is assumed.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- At unit velocity the difference of two complex resolvents
factors into a product of resolvents. -/
theorem massiveDiracUnitResolvent_inverse_sub
    (s t q : ℂ) (hs : s - q ≠ 0) (ht : t - q ≠ 0) :
    (s - q)⁻¹ - (t - q)⁻¹ =
      (t - s) * ((s - q)⁻¹ * (t - q)⁻¹) := by
  field_simp [hs, ht]
  ring

/-- The absolutely-decaying two-resolvent kernel that occurs in
the spectral difference of two unit-velocity radial Green functions. -/
noncomputable def massiveDiracUnitResolventDifferenceKernel
    (c : ℝ) (s t : ℂ) (p : ℝ) : ℂ :=
  (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
    ((s - ((p ^ 2 : ℝ) : ℂ))⁻¹ *
      (t - ((p ^ 2 : ℝ) : ℂ))⁻¹)

/-- Nonreal spectral centers have no real radial-momentum poles. -/
theorem massiveDiracUnitResolvent_den_ne_zero (s : ℂ)
    (hs : s.im ≠ 0) (p : ℝ) :
    s - ((p ^ 2 : ℝ) : ℂ) ≠ 0 := by
  intro heq
  have him := congrArg Complex.im heq
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero,
    Complex.zero_im] at him
  exact hs him

/-- The finite-cutoff radial Fourier resolvent difference is exactly
a two-denominator integral, with no limit or distributional prescription. -/
theorem massiveDiracUnitResolvent_integral_sub
    (c b : ℝ) (s t : ℂ) (hs : s.im ≠ 0) (ht : t.im ≠ 0) :
    (∫ p in (0 : ℝ)..b,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
        (s - ((p ^ 2 : ℝ) : ℂ))⁻¹) -
    (∫ p in (0 : ℝ)..b,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
        (t - ((p ^ 2 : ℝ) : ℂ))⁻¹) =
      (t - s) *
        (∫ p in (0 : ℝ)..b,
          massiveDiracUnitResolventDifferenceKernel c s t p) := by
  let f : ℝ → ℂ := fun p =>
    (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
      (s - ((p ^ 2 : ℝ) : ℂ))⁻¹
  let g : ℝ → ℂ := fun p =>
    (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
      (t - ((p ^ 2 : ℝ) : ℂ))⁻¹
  have hK : Continuous (fun p : ℝ =>
      polarFourierZerothAngularKernel (p * c)) :=
    continuous_polarFourierZerothAngularKernel.comp
      (continuous_id.mul continuous_const)
  have hInvS : Continuous (fun p : ℝ =>
      (s - ((p ^ 2 : ℝ) : ℂ))⁻¹) := by
    have hden : Continuous (fun p : ℝ =>
        s - ((p ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact hden.inv₀ (massiveDiracUnitResolvent_den_ne_zero s hs)
  have hInvT : Continuous (fun p : ℝ =>
      (t - ((p ^ 2 : ℝ) : ℂ))⁻¹) := by
    have hden : Continuous (fun p : ℝ =>
        t - ((p ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact hden.inv₀ (massiveDiracUnitResolvent_den_ne_zero t ht)
  have hf : Continuous f :=
    ((Complex.continuous_ofReal.comp continuous_id).mul hK).mul hInvS
  have hg : Continuous g :=
    ((Complex.continuous_ofReal.comp continuous_id).mul hK).mul hInvT
  have hpoint (p : ℝ) :
      f p - g p = (t - s) *
        massiveDiracUnitResolventDifferenceKernel c s t p := by
    dsimp only [f, g, massiveDiracUnitResolventDifferenceKernel]
    rw [show
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (s - ((p ^ 2 : ℝ) : ℂ))⁻¹ -
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (t - ((p ^ 2 : ℝ) : ℂ))⁻¹ =
        ((p : ℂ) * polarFourierZerothAngularKernel (p * c)) *
          ((s - ((p ^ 2 : ℝ) : ℂ))⁻¹ -
            (t - ((p ^ 2 : ℝ) : ℂ))⁻¹) by ring]
    rw [massiveDiracUnitResolvent_inverse_sub s t
      ((p ^ 2 : ℝ) : ℂ)
      (massiveDiracUnitResolvent_den_ne_zero s hs p)
      (massiveDiracUnitResolvent_den_ne_zero t ht p)]
    ring
  change (∫ p in (0 : ℝ)..b, f p) -
      (∫ p in (0 : ℝ)..b, g p) =
        (t - s) *
          (∫ p in (0 : ℝ)..b,
            massiveDiracUnitResolventDifferenceKernel c s t p)
  calc
    (∫ p in (0 : ℝ)..b, f p) -
        (∫ p in (0 : ℝ)..b, g p) =
      ∫ p in (0 : ℝ)..b, f p - g p :=
        (intervalIntegral.integral_sub
          (hf.intervalIntegrable 0 b) (hg.intervalIntegrable 0 b)).symm
    _ = ∫ p in (0 : ℝ)..b,
          (t - s) * massiveDiracUnitResolventDifferenceKernel c s t p := by
      apply intervalIntegral.integral_congr
      intro p _
      exact hpoint p
    _ = (t - s) *
          (∫ p in (0 : ℝ)..b,
            massiveDiracUnitResolventDifferenceKernel c s t p) :=
      intervalIntegral.integral_const_mul

/-- The already-proved oscillatory Fourier UV limits show that the
difference of two centers converges to a *single* two-resolvent integral
with the exact spectral difference prefactor.

A separate absolute-integrability argument is needed to identify the
right side with a Lebesgue integral over `Set.Ioi 0`. -/
theorem massiveDiracUnitResolvent_difference_tendsto
    (c : ℝ) (s t : ℂ)
    (hc : c ≠ 0) (hs : s.im ≠ 0) (ht : t.im ≠ 0) :
    Filter.Tendsto
      (fun b : ℝ =>
        (t - s) *
          (∫ p in (0 : ℝ)..b,
            massiveDiracUnitResolventDifferenceKernel c s t p))
      Filter.atTop
      (nhds (massiveDiracRadialFourierUVCenter 1 c s -
        massiveDiracRadialFourierUVCenter 1 c t)) := by
  have hUVs :
      Filter.Tendsto
        (fun b : ℝ => ∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (s - ((p ^ 2 : ℝ) : ℂ))⁻¹)
        Filter.atTop (nhds (massiveDiracRadialFourierUVCenter 1 c s)) := by
    simpa only [one_pow, one_mul] using
      (massiveDiracRadialFourier_tendsto_uvValue_center
        1 c s (by norm_num) hc hs)
  have hUVt :
      Filter.Tendsto
        (fun b : ℝ => ∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (t - ((p ^ 2 : ℝ) : ℂ))⁻¹)
        Filter.atTop (nhds (massiveDiracRadialFourierUVCenter 1 c t)) := by
    simpa only [one_pow, one_mul] using
      (massiveDiracRadialFourier_tendsto_uvValue_center
        1 c t (by norm_num) hc ht)
  exact (hUVs.sub hUVt).congr'
    (Filter.Eventually.of_forall fun b =>
      (massiveDiracUnitResolvent_integral_sub c b s t hs ht).symm)

end

end QuantumTheory.Models.MassiveDirac
