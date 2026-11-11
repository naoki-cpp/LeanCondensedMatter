import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialScalarTail
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Explicit finite-part boundary for the radial Dirac Fourier resolvent

A fixed complex spectral center with nonzero imaginary part defines an
unambiguous momentum-UV limit of the zeroth-harmonic radial Green kernel
at nonzero real-space separation. Unlike a bare existence statement,
the result identifies its value as a **finite low-momentum K0 integral**
plus an **absolutely integrable K1 resolvent-squared remainder**.
The integration-by-parts boundary term is explicitly retained.

The auxiliary scale separating the low-momentum integral and UV tail
is proved irrelevant, provided it exceeds the quadratic-dominance
threshold. This is a mathematical finite-part representation suitable
for later outgoing/Hankel boundary identification.

The spectral energy and mass here are *fixed*. The physical Born
self-energy at nonzero disorder diverges in the unrenormalized UV
limit; the conclusions below must not be applied to running
finite-cutoff Born effective parameters without a separately proved
renormalization/uniform-convergence result.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- The exact finite-part value obtained by integrating the oscillatory
K0 kernel from zero to an auxiliary scale and integrating the K1 tail
by parts. The UV remainder is absolutely integrable under the hypotheses
of the corresponding convergence theorem. -/
noncomputable def massiveDiracRadialFourierUVFinitePartCenter
    (v c a : ℝ) (center : ℂ) : ℂ :=
  (∫ p in (0 : ℝ)..a,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
        (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) +
    ((-((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) *
        (center - ((v ^ 2 * a ^ 2 : ℝ) : ℂ))⁻¹) -
      ∫ p in Set.Ioi a,
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹ ^ 2)) /
      (Complex.I * (c : ℂ)))

/-- The finite-part expression is exactly the cutoff limit of the
original radial K0 Fourier integral, with no missing endpoint term.
A genuine UV-integrability proof for the K1 remainder and the
vanishing first-harmonic boundary term are both consumed here. -/
theorem massiveDiracRadialFourier_tendsto_uvFinitePartAt_center
    (v c a : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)) ≠ 0)
    (ha : max (1 : ℝ) (2 * ‖center‖ / v ^ 2) ≤ a) :
    Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹)
      Filter.atTop (nhds
        (massiveDiracRadialFourierUVFinitePartCenter v c a (center))) := by
  let f : ℝ → ℂ := fun p =>
    (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
      ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹
  have htail :=
    tendsto_integral_massiveDiracRadialCenter_inv_fourierKernel_of_conditions
      v c a center hc hden
      (massiveDiracRadialFourierRemainder_integrableOn_uv_center
        v c a center hv hden ha)
      (massiveDiracRadialCenter_firstHarmonicBoundary_tendsto_zero
        v c center hv)
  have hDcont :
      Continuous (fun p : ℝ => (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))) := by
    fun_prop
  have hInvCont :
      Continuous (fun p : ℝ => ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹) :=
    hDcont.inv₀ hden
  have hKcont :
      Continuous (fun p : ℝ => polarFourierZerothAngularKernel (p * c)) :=
    continuous_polarFourierZerothAngularKernel.comp
      (continuous_id.mul continuous_const)
  have hf : Continuous f :=
    ((Complex.continuous_ofReal.comp continuous_id).mul hKcont).mul hInvCont
  have hleft : IntervalIntegrable f volume (0 : ℝ) a :=
    hf.intervalIntegrable _ _
  have hsplit (b : ℝ) :
      (∫ p in (0 : ℝ)..b, f p) =
        (∫ p in (0 : ℝ)..a, f p) + (∫ p in a..b, f p) :=
    (intervalIntegral.integral_add_adjacent_intervals hleft
      (hf.intervalIntegrable a b)).symm
  have hconst :
      Filter.Tendsto
        (fun _ : ℝ => ∫ p in (0 : ℝ)..a, f p)
        Filter.atTop (nhds (∫ p in (0 : ℝ)..a, f p)) :=
    tendsto_const_nhds
  have hsum := hconst.add htail
  change Filter.Tendsto (fun b : ℝ => ∫ p in (0 : ℝ)..b, f p)
    Filter.atTop
    (nhds ((∫ p in (0 : ℝ)..a, f p) +
      ((-((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) *
          ((center - ((v ^ 2 * a ^ 2 : ℝ) : ℂ)))⁻¹) -
        ∫ p in Set.Ioi a,
          (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
            ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
              ((center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)))⁻¹ ^ 2)) /
        (Complex.I * (c : ℂ)))))
  exact hsum.congr' (Filter.Eventually.of_forall fun b => (hsplit b).symm)


/-- Energy/mass specialization of the center-indexed Fourier finite-part limit. -/
theorem massiveDiracRadialFourier_tendsto_uvFinitePartAt
    (v c a : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0)
    (ha : max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ a) :
    Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹)
      Filter.atTop (nhds
        (massiveDiracRadialFourierUVFinitePartCenter v c a (energy ^ 2 - mass ^ 2))) := by
  have hcenter (p : ℝ) :
      energy ^ 2 - mass ^ 2 - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [massiveDiracRadialDenominator] using hden p
  simpa only [massiveDiracRadialDenominator] using
    massiveDiracRadialFourier_tendsto_uvFinitePartAt_center
      v c a (energy ^ 2 - mass ^ 2) hv hc hcenter ha

/-- The original existential Fourier UV limit follows from the explicit
finite-part boundary, without repeating the low-momentum/tail split proof. -/
theorem massiveDiracRadialFourierKernel_tendsto_atTop
    (v c : ℝ) (energy mass : ℂ) (hv : v ≠ 0) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0) :
    ∃ value : ℂ, Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹)
      Filter.atTop (nhds value) := by
  exact ⟨massiveDiracRadialFourierUVFinitePartCenter
      v c (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2))
        (energy ^ 2 - mass ^ 2),
    massiveDiracRadialFourier_tendsto_uvFinitePartAt
      v c (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2))
      energy mass hv hc hden le_rfl⟩

/-- The auxiliary splitting scale does not affect the UV finite part:
both expressions are limits of the same cutoff Fourier integral. -/
theorem massiveDiracRadialFourierUVFinitePartCenter_eq_of_scales
    (v c a b : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0)
    (ha : max (1 : ℝ) (2 * ‖center‖ / v ^ 2) ≤ a)
    (hb : max (1 : ℝ) (2 * ‖center‖ / v ^ 2) ≤ b) :
    massiveDiracRadialFourierUVFinitePartCenter v c a center =
      massiveDiracRadialFourierUVFinitePartCenter v c b center := by
  exact tendsto_nhds_unique
    (massiveDiracRadialFourier_tendsto_uvFinitePartAt_center
      v c a center hv hc hden ha)
    (massiveDiracRadialFourier_tendsto_uvFinitePartAt_center
      v c b center hv hc hden hb)

/-- A canonical finite-part choice of scale, just above the proved
quadratic-dominance threshold. The resulting value does not depend
on any other valid splitting scale. -/
noncomputable def massiveDiracRadialFourierUVCenter
    (v c : ℝ) (center : ℂ) : ℂ :=
  massiveDiracRadialFourierUVFinitePartCenter
    v c (max (1 : ℝ) (2 * ‖center‖ / v ^ 2)) center

/-- The canonical UV Fourier value is the nonreal-center
finite-part limit, without choosing a square-root branch. -/
theorem massiveDiracRadialFourier_tendsto_uvValue_center
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹)
      Filter.atTop (nhds (massiveDiracRadialFourierUVCenter v c center)) := by
  have hden (p : ℝ) :
      center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ) ≠ 0 := by
    intro hzero
    have him :
        (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ)).im = center.im := by
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    have himzero := congrArg Complex.im hzero
    rw [him] at himzero
    exact hcenter (by simpa using himzero)
  unfold massiveDiracRadialFourierUVCenter
  exact massiveDiracRadialFourier_tendsto_uvFinitePartAt_center
    v c (max (1 : ℝ) (2 * ‖center‖ / v ^ 2)) center hv hc hden le_rfl

/-- Evenness is inherited from the finite-cutoff angular kernel, without
a choice of square-root branch or a running Born limit. -/
theorem massiveDiracRadialFourierUVCenter_neg
    (v c : ℝ) (center : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0) (hcenter : center.im ≠ 0) :
    massiveDiracRadialFourierUVCenter v (-c) center =
      massiveDiracRadialFourierUVCenter v c center := by
  have hneg := massiveDiracRadialFourier_tendsto_uvValue_center
    v (-c) center hv (neg_ne_zero.mpr hc) hcenter
  have hpos := massiveDiracRadialFourier_tendsto_uvValue_center
    v c center hv hc hcenter
  have heq (b : ℝ) :
      (∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * -c) *
          (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) =
        (∫ p in (0 : ℝ)..b,
          (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
            (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹) := by
    apply intervalIntegral.integral_congr
    intro p _
    dsimp only
    rw [show p * -c = -(p * c) by ring,
      polarFourierZerothAngularKernel_neg]
  exact tendsto_nhds_unique
    (hneg.congr' (Filter.Eventually.of_forall heq))
    hpos

open scoped ComplexConjugate

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
  let f : ℝ → ℂ := fun p =>
    (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
      (center - ((v ^ 2 * p ^ 2 : ℝ) : ℂ))⁻¹
  change conj (∫ p in (0 : ℝ)..b, f p) = _
  calc
    conj (∫ p in (0 : ℝ)..b, f p) =
        ∫ p in (0 : ℝ)..b, conj (f p) := by
      simpa using
        ((Complex.conjLIE.toLinearIsometry).intervalIntegral_comp_comm
          (f := f) (a := (0 : ℝ)) (b := b)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro p _
      simp only [f, map_mul, Complex.conj_inv, Complex.conj_ofReal,
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
