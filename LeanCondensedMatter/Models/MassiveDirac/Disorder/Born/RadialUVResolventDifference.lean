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

Here we prove the exact two-resolvent identity at every finite cutoff,
the explicit UV norm bound, genuine absolute integrability on the
positive half-line, and equality with the difference of the existing
proven UV values. No Hankel evaluation is assumed.
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
      (intervalIntegral.integral_const_mul (t - s)
        (massiveDiracUnitResolventDifferenceKernel c s t))

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
      massiveDiracUnitResolvent_integral_sub c b s t hs ht)


/-- On the ultraviolet half-line the two-center resolvent difference
decays like `p⁻³`, including the radial Jacobian. No asymptotic
expansion of Bessel functions is needed: the full-angle Fourier
kernel is uniformly bounded by `2π`. -/
theorem massiveDiracUnitResolventDifferenceKernel_norm_le
    (c p : ℝ) (s t : ℂ)
    (hp : max (max 1 (2 * ‖s‖)) (max 1 (2 * ‖t‖)) ≤ p) :
    ‖massiveDiracUnitResolventDifferenceKernel c s t p‖ ≤
      (8 * Real.pi) * p ^ (-3 : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p :=
    ((le_max_left (1 : ℝ) (2 * ‖s‖)).trans
      (le_max_left (max 1 (2 * ‖s‖)) (max 1 (2 * ‖t‖)))).trans hp
  have hp0 : 0 < p := by linarith
  have hsBound :
      ‖(s - ((p ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ (p ^ 2 / 2)⁻¹ := by
    simpa only [one_pow, one_mul, div_one] using
      (massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
        1 p s (by norm_num) (by
          simpa only [one_pow, div_one] using
            ((le_max_left (max 1 (2 * ‖s‖))
              (max 1 (2 * ‖t‖))).trans hp)))
  have htBound :
      ‖(t - ((p ^ 2 : ℝ) : ℂ))⁻¹‖ ≤ (p ^ 2 / 2)⁻¹ := by
    simpa only [one_pow, one_mul, div_one] using
      (massiveDiracRadialCenter_inv_norm_le_half_quadratic_inv
        1 p t (by norm_num) (by
          simpa only [one_pow, div_one] using
            ((le_max_right (max 1 (2 * ‖s‖))
              (max 1 (2 * ‖t‖))).trans hp)))
  have hK := polarFourierZerothAngularKernel_norm_le (p * c)
  have hnorm :
      ‖massiveDiracUnitResolventDifferenceKernel c s t p‖ =
        p * ‖polarFourierZerothAngularKernel (p * c)‖ *
          ‖(s - ((p ^ 2 : ℝ) : ℂ))⁻¹‖ *
          ‖(t - ((p ^ 2 : ℝ) : ℂ))⁻¹‖ := by
    simp only [massiveDiracUnitResolventDifferenceKernel,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    ring
  rw [hnorm]
  calc
    p * ‖polarFourierZerothAngularKernel (p * c)‖ *
        ‖(s - ((p ^ 2 : ℝ) : ℂ))⁻¹‖ *
        ‖(t - ((p ^ 2 : ℝ) : ℂ))⁻¹‖ ≤
      p * (2 * Real.pi) * (p ^ 2 / 2)⁻¹ * (p ^ 2 / 2)⁻¹ := by
        gcongr
    _ = (8 * Real.pi) / p ^ 3 := by
      field_simp [ne_of_gt hp0]
      ring
    _ = (8 * Real.pi) * p ^ (-3 : ℝ) := by
      simp only [Real.rpow_neg hp0.le, div_eq_mul_inv]

/-- The two-resolvent spectral-difference kernel is genuinely Bochner
integrable over all positive momenta, unlike either single-center
oscillatory Fourier integral. -/
theorem massiveDiracUnitResolventDifferenceKernel_integrableOn
    (c : ℝ) (s t : ℂ) (hs : s.im ≠ 0) (ht : t.im ≠ 0) :
    IntegrableOn
      (massiveDiracUnitResolventDifferenceKernel c s t)
      (Set.Ioi (0 : ℝ)) := by
  let a : ℝ := max (max 1 (2 * ‖s‖)) (max 1 (2 * ‖t‖))
  have ha1 : (1 : ℝ) ≤ a := by
    dsimp [a]
    exact (le_max_left (1 : ℝ) (2 * ‖s‖)).trans
      (le_max_left (max 1 (2 * ‖s‖)) (max 1 (2 * ‖t‖)))
  have ha0 : (0 : ℝ) < a := by linarith
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
  have hcont :
      Continuous (massiveDiracUnitResolventDifferenceKernel c s t) := by
    unfold massiveDiracUnitResolventDifferenceKernel
    exact ((Complex.continuous_ofReal.comp continuous_id).mul hK).mul
      (hInvS.mul hInvT)
  have hnear : IntegrableOn
      (massiveDiracUnitResolventDifferenceKernel c s t)
      (Set.Ioc 0 a) := hcont.integrableOn_Ioc
  have hpow : IntegrableOn (fun p : ℝ => p ^ (-3 : ℝ)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha0
  have hmajor :
      IntegrableOn (fun p : ℝ => (8 * Real.pi) * p ^ (-3 : ℝ))
        (Set.Ioi a) := hpow.const_mul _
  have htail : IntegrableOn
      (massiveDiracUnitResolventDifferenceKernel c s t)
      (Set.Ioi a) := by
    apply hmajor.mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact massiveDiracUnitResolventDifferenceKernel_norm_le
      c p s t (by simpa only [a] using (le_of_lt hp))
  rw [← Set.Ioc_union_Ioi_eq_Ioi ha0.le]
  exact hnear.union htail

/-- The center difference of the ultraviolet Fourier Green functions
is a single **absolutely convergent** complex Lebesgue integral.
The proof uses a finite-cutoff resolvent identity and uniqueness
of the two already established spectral-center UV limits.
This is the analytic Stieltjes bridge toward the still-unproved
individual Fourier–Hankel transform. -/
theorem massiveDiracUnitResolvent_UVCenter_sub_eq_integral
    (c : ℝ) (s t : ℂ)
    (hc : c ≠ 0) (hs : s.im ≠ 0) (ht : t.im ≠ 0) :
    massiveDiracRadialFourierUVCenter 1 c s -
      massiveDiracRadialFourierUVCenter 1 c t =
        (t - s) *
          (∫ p in Set.Ioi (0 : ℝ),
            massiveDiracUnitResolventDifferenceKernel c s t p) := by
  have hint :=
    massiveDiracUnitResolventDifferenceKernel_integrableOn c s t hs ht
  have habs :
      Filter.Tendsto
        (fun b : ℝ =>
          (t - s) * (∫ p in (0 : ℝ)..b,
            massiveDiracUnitResolventDifferenceKernel c s t p))
        Filter.atTop
        (nhds ((t - s) * (∫ p in Set.Ioi (0 : ℝ),
          massiveDiracUnitResolventDifferenceKernel c s t p))) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hint Filter.tendsto_id).const_mul _
  exact tendsto_nhds_unique
    (massiveDiracUnitResolvent_difference_tendsto c s t hc hs ht)
    habs

end

end QuantumTheory.Models.MassiveDirac
