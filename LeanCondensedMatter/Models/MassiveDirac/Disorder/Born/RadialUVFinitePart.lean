import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialScalarTail
import Mathlib.Tactic.FunProp

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
limit (#4509); the conclusions below must not be applied to running
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
noncomputable def massiveDiracRadialFourierUVFinitePartAt
    (v c a : ℝ) (energy mass : ℂ) : ℂ :=
  (∫ p in (0 : ℝ)..a,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
        (massiveDiracRadialDenominator v p energy mass)⁻¹) +
    ((-((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) *
        (massiveDiracRadialDenominator v a energy mass)⁻¹) -
      ∫ p in Set.Ioi a,
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)) /
      (Complex.I * (c : ℂ)))

/-- The finite-part expression is exactly the cutoff limit of the
original radial K0 Fourier integral, with no missing endpoint term.
A genuine UV-integrability proof for the K1 remainder and the
vanishing first-harmonic boundary term are both consumed here. -/
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
        (massiveDiracRadialFourierUVFinitePartAt v c a energy mass)) := by
  let f : ℝ → ℂ := fun p =>
    (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
      (massiveDiracRadialDenominator v p energy mass)⁻¹
  have htail :=
    tendsto_integral_massiveDiracRadialDenominator_inv_fourierKernel_of_conditions
      v c a energy mass hc hden
      (massiveDiracRadialFourierRemainder_integrableOn_uv
        v c a energy mass hv hden ha)
      (massiveDiracRadialDenominator_firstHarmonicBoundary_tendsto_zero
        v c energy mass hv)
  have hDcont :
      Continuous (fun p : ℝ => massiveDiracRadialDenominator v p energy mass) := by
    unfold massiveDiracRadialDenominator
    fun_prop
  have hInvCont :
      Continuous (fun p : ℝ => (massiveDiracRadialDenominator v p energy mass)⁻¹) :=
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
          (massiveDiracRadialDenominator v a energy mass)⁻¹) -
        ∫ p in Set.Ioi a,
          (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
            ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
              (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)) /
        (Complex.I * (c : ℂ)))))
  exact hsum.congr' (Filter.Eventually.of_forall fun b => (hsplit b).symm)

/-- Independence of the arbitrary UV splitting scale. Both finite-part
expressions are proved limits of **the same** physical K0 Fourier
integral; their equality is not imposed as a renormalization axiom. -/
theorem massiveDiracRadialFourierUVFinitePartAt_eq_of_scales
    (v c a b : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0)
    (ha : max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ a)
    (hb : max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ b) :
    massiveDiracRadialFourierUVFinitePartAt v c a energy mass =
      massiveDiracRadialFourierUVFinitePartAt v c b energy mass := by
  exact tendsto_nhds_unique
    (massiveDiracRadialFourier_tendsto_uvFinitePartAt
      v c a energy mass hv hc hden ha)
    (massiveDiracRadialFourier_tendsto_uvFinitePartAt
      v c b energy mass hv hc hden hb)

/-- A nonreal quadratic spectral center excludes real radial poles,
without requiring the energy or mass to be individually nonreal. -/
theorem massiveDiracRadialDenominator_ne_zero_of_center_im_ne_zero
    (v p : ℝ) (energy mass : ℂ)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    massiveDiracRadialDenominator v p energy mass ≠ 0 := by
  intro hzero
  have him :
      (massiveDiracRadialDenominator v p energy mass).im =
        (energy ^ 2 - mass ^ 2).im := by
    unfold massiveDiracRadialDenominator
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  have himzero := congrArg Complex.im hzero
  rw [him] at himzero
  exact hcenter (by simpa using himzero)

/-- A canonical finite-part choice of scale, just above the proved
quadratic-dominance threshold. The resulting value does not depend
on any other valid splitting scale. -/
noncomputable def massiveDiracRadialFourierUVValue
    (v c : ℝ) (energy mass : ℂ) : ℂ :=
  massiveDiracRadialFourierUVFinitePartAt
    v c (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2)) energy mass

/-- Concrete, finite and cutoff-independent Fourier UV value at any
nonzero spatial Fourier scale, provided the spectral center remains
strictly away from the real axis. -/
theorem massiveDiracRadialFourier_tendsto_uvValue
    (v c : ℝ) (energy mass : ℂ)
    (hv : v ≠ 0) (hc : c ≠ 0)
    (hcenter : (energy ^ 2 - mass ^ 2).im ≠ 0) :
    Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹)
      Filter.atTop (nhds (massiveDiracRadialFourierUVValue v c energy mass)) := by
  unfold massiveDiracRadialFourierUVValue
  exact massiveDiracRadialFourier_tendsto_uvFinitePartAt
    v c (max (1 : ℝ) (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2))
    energy mass hv hc
    (fun p => massiveDiracRadialDenominator_ne_zero_of_center_im_ne_zero
      v p energy mass hcenter)
    le_rfl

end

end QuantumTheory.Models.MassiveDirac
