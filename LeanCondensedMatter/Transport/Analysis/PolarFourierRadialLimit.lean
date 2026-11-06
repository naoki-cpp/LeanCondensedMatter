import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialPrimitive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option linter.style.header false

/-!
# Radial Fourier improper limit from the first-harmonic primitive

The ultraviolet cutoff can be removed from a weighted zeroth-harmonic radial
integral when (1) the first-harmonic boundary term tends to zero and
(2) its weighted derivative is integrable over a positive half-line.
Unlike a formal asymptotic series, this theorem gives a precise finite-cutoff
limit formula, with analytic hypotheses explicit for each physical weight.
-/

namespace QuantumTheory.Transport

noncomputable section

open MeasureTheory
open Filter
open scoped Interval

/-- A convergence bridge for finite radial Fourier transforms. The first
angular harmonic is a primitive of the zeroth angular harmonic and the
infinite-cutoff limit is precisely the integral of the derivative term.
The hypotheses concern only the ultraviolet boundary and its integrability;
they are not silently discharged by the finite-cutoff part-integration law. -/
theorem tendsto_integral_polarFourierZerothAngularKernel_of_by_parts
    (c a : ℝ) (hc : c ≠ 0)
    (weight weight' : ℝ → ℂ)
    (hweight : ∀ p : ℝ, HasDerivAt weight (weight' p) p)
    (hweight' : Continuous weight')
    (hint : IntegrableOn
      (fun p : ℝ => (p : ℂ) *
        polarFourierFirstCosineAngularKernel (p * c) * weight' p)
      (Set.Ioi a))
    (hboundary : Tendsto
      (fun b : ℝ => (b : ℂ) *
        polarFourierFirstCosineAngularKernel (b * c) * weight b)
      atTop (nhds 0)) :
    Tendsto
      (fun b : ℝ => ∫ p in a..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) * weight p)
      atTop
      (nhds ((-((a : ℂ) *
          polarFourierFirstCosineAngularKernel (a * c) * weight a) -
        ∫ p in Set.Ioi a, (p : ℂ) *
          polarFourierFirstCosineAngularKernel (p * c) * weight' p) /
          (Complex.I * (c : ℂ)))) := by
  let boundary : ℝ → ℂ := fun t =>
    (t : ℂ) * polarFourierFirstCosineAngularKernel (t * c) * weight t
  let remainder : ℝ → ℂ := fun t =>
    (t : ℂ) * polarFourierFirstCosineAngularKernel (t * c) * weight' t
  have hrem : Tendsto
      (fun b : ℝ => ∫ p in a..b, remainder p)
      atTop (nhds (∫ p in Set.Ioi a, remainder p)) :=
    intervalIntegral_tendsto_integral_Ioi a hint tendsto_id
  have hnum : Tendsto
      (fun b : ℝ => boundary b - boundary a - ∫ p in a..b, remainder p)
      atTop
      (nhds (-(boundary a) - ∫ p in Set.Ioi a, remainder p)) := by
    simpa only [zero_sub] using
      ((hboundary.sub_const (boundary a)).sub hrem)
  have hfactor : Complex.I * (c : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hc)
  have hlim := hnum.div_const (Complex.I * (c : ℂ))
  have hrewrite (b : ℝ) :
      (∫ p in a..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) * weight p) =
      (boundary b - boundary a - ∫ p in a..b, remainder p) /
        (Complex.I * (c : ℂ)) := by
    apply (eq_div_iff hfactor).2
    have h := integral_polarFourierZerothAngularKernel_mul_weight_by_parts
      c a b weight weight' hweight hweight'
    simpa only [boundary, remainder, mul_comm] using h
  change Tendsto
    (fun b : ℝ => ∫ p in a..b,
      (p : ℂ) * polarFourierZerothAngularKernel (p * c) * weight p)
    atTop
    (nhds ((-(boundary a) - ∫ p in Set.Ioi a, remainder p) /
      (Complex.I * (c : ℂ))))
  exact hlim.congr' (Filter.Eventually.of_forall (fun b => (hrewrite b).symm))

end

end QuantumTheory.Transport
