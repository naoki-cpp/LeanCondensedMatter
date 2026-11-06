import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialScalarGenerator
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBound
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVIntegrability
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialPrimitive
import LeanCondensedMatter.Transport.Analysis.PolarFourierRadialLimit
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Radial scalar Green kernel: finite-cutoff ultraviolet tail decomposition

The Fourier first-harmonic primitive yields an exact integration-by-parts
decomposition of the complex quadratic Dirac resolvent kernel. In
contrast with a naive absolute-convergence assertion for the K0 transform,
this identity exposes the ultraviolet boundary term and the differentiated
resolvent term separately. The finite-broadening Born-Dyson specialization
inherits it without changing the model or taking any regulator limits.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval

/-- The inverse of the massive-Dirac quadratic radial denominator has an
explicit real-radial derivative whenever the denominator stays nonzero. -/
theorem massiveDiracRadialDenominator_inv_hasDerivAt
    (v p : ℝ) (energy mass : ℂ)
    (hden : massiveDiracRadialDenominator v p energy mass ≠ 0) :
    HasDerivAt
      (fun q : ℝ => (massiveDiracRadialDenominator v q energy mass)⁻¹)
      ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
        (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2) p := by
  have hcomplex :
      HasDerivAt
        (fun z : ℂ => energy ^ 2 - mass ^ 2 - (v : ℂ) ^ 2 * z ^ 2)
        (-2 * (v : ℂ) ^ 2 * (p : ℂ)) (p : ℂ) := by
    convert (hasDerivAt_const (p : ℂ) (energy ^ 2 - mass ^ 2)).sub
        (((hasDerivAt_id (p : ℂ)).pow 2).const_mul ((v : ℂ) ^ 2)) using 1 <;>
      first | rfl | (simp only [id]; ring)
  have hD :
      HasDerivAt (fun q : ℝ => massiveDiracRadialDenominator v q energy mass)
        (-2 * (v : ℂ) ^ 2 * (p : ℂ)) p := by
    convert hcomplex.comp_ofReal using 1
    funext q
    unfold massiveDiracRadialDenominator
    push_cast
    ring
  have hinv := hD.fun_inv hden
  convert hinv using 1
  · rw [div_eq_mul_inv, inv_pow]
    ring

/-- Exact finite-interval integration by parts for a quadratic Dirac
resolvent, stated without a Born approximation. The derivative factor on
the final integral has two additional inverse denominators. -/
theorem integral_massiveDiracRadialDenominator_inv_fourierKernel_by_parts
    (v c a b : ℝ) (energy mass : ℂ)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0) :
    (Complex.I * (c : ℂ)) *
        (∫ p in a..b, (p : ℂ) *
          polarFourierZerothAngularKernel (p * c) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹) =
      ((b : ℂ) * polarFourierFirstCosineAngularKernel (b * c) *
        (massiveDiracRadialDenominator v b energy mass)⁻¹) -
      ((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) *
        (massiveDiracRadialDenominator v a energy mass)⁻¹) -
      (∫ p in a..b,
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)) := by
  have hDcont : Continuous
      (fun p : ℝ => massiveDiracRadialDenominator v p energy mass) := by
    unfold massiveDiracRadialDenominator
    fun_prop
  have hInvCont : Continuous
      (fun p : ℝ => (massiveDiracRadialDenominator v p energy mass)⁻¹) :=
    hDcont.inv₀ hden
  have hDerivativeCont : Continuous
      (fun p : ℝ =>
        (2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2) := by
    exact ((continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_id)).mul
        (hInvCont.pow 2))
  exact integral_polarFourierZerothAngularKernel_mul_weight_by_parts
    c a b
    (fun p : ℝ => (massiveDiracRadialDenominator v p energy mass)⁻¹)
    (fun p : ℝ => (2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
      (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)
    (fun p => massiveDiracRadialDenominator_inv_hasDerivAt v p energy mass (hden p))
    hDerivativeCont

/-- The finite-broadening Born-Dyson scalar Fourier kernel inherits the
exact ultraviolet integration-by-parts identity with the *physical*
retarded/advanced complex effective energy and mass, before any cutoff
or broadening limit. -/
theorem finiteCutoffContinuumBornDysonRadialScalarKernel_by_parts
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax c a b : ℝ)
    (hbroadening : broadening ≠ 0) (hdisorder : 0 ≤ disorderStrength)
    (hpMax : 0 ≤ pMax) :
    let D := fun p : ℝ => finiteCutoffContinuumBornDysonDenominator
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
    (Complex.I * (c : ℂ)) *
        (∫ p in a..b, (p : ℂ) *
          polarFourierZerothAngularKernel (p * c) * (D p)⁻¹) =
      ((b : ℂ) * polarFourierFirstCosineAngularKernel (b * c) * (D b)⁻¹) -
      ((a : ℂ) * polarFourierFirstCosineAngularKernel (a * c) * (D a)⁻¹) -
      (∫ p in a..b,
        (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) * (D p)⁻¹ ^ 2)) := by
  have hden (p : ℝ) :
      massiveDiracRadialDenominator v p
        (finiteCutoffContinuumBornEffectiveEnergy
          side v m probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornEffectiveMass
          side v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0 := by
    rw [finiteCutoffContinuumBornDysonDenominator_eq_radial]
    exact finiteCutoffContinuumBornDysonDenominator_ne_zero
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax
      hbroadening hdisorder hpMax
  have h := integral_massiveDiracRadialDenominator_inv_fourierKernel_by_parts
    v c a b
    (finiteCutoffContinuumBornEffectiveEnergy
      side v m probeEnergy broadening disorderStrength hbar pMax)
    (finiteCutoffContinuumBornEffectiveMass
      side v m probeEnergy broadening disorderStrength hbar pMax)
    hden
  dsimp only
  simpa only [finiteCutoffContinuumBornDysonDenominator_eq_radial] using h

/-- A cutoff limit theorem for a quadratic massive-Dirac Fourier resolvent,
assuming exactly the two ultraviolet conditions isolated by the preceding
finite-interval integration-by-parts theorem. This statement keeps the
complex spectral center fixed while its radial integration cutoff increases.
It does not take the cutoff of a self-consistent Born self-energy. -/
theorem tendsto_integral_massiveDiracRadialDenominator_inv_fourierKernel_of_conditions
    (v c a : ℝ) (energy mass : ℂ) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0)
    (hint : IntegrableOn (fun p : ℝ =>
      (p : ℂ) * polarFourierFirstCosineAngularKernel (p * c) *
        ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2))
      (Set.Ioi a))
    (hboundary : Filter.Tendsto (fun b : ℝ =>
      (b : ℂ) * polarFourierFirstCosineAngularKernel (b * c) *
        (massiveDiracRadialDenominator v b energy mass)⁻¹)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun b : ℝ => ∫ p in a..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹)
      Filter.atTop
      (nhds ((-((a : ℂ) *
          polarFourierFirstCosineAngularKernel (a * c) *
          (massiveDiracRadialDenominator v a energy mass)⁻¹) -
        ∫ p in Set.Ioi a, (p : ℂ) *
          polarFourierFirstCosineAngularKernel (p * c) *
          ((2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
            (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)) /
        (Complex.I * (c : ℂ)))) := by
  have hDcont : Continuous
      (fun p : ℝ => massiveDiracRadialDenominator v p energy mass) := by
    unfold massiveDiracRadialDenominator
    fun_prop
  have hInvCont : Continuous
      (fun p : ℝ => (massiveDiracRadialDenominator v p energy mass)⁻¹) :=
    hDcont.inv₀ hden
  have hDerivativeCont : Continuous
      (fun p : ℝ =>
        (2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2) :=
    ((continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_id)).mul
        (hInvCont.pow 2))
  exact tendsto_integral_polarFourierZerothAngularKernel_of_by_parts
    c a hc
    (fun p : ℝ => (massiveDiracRadialDenominator v p energy mass)⁻¹)
    (fun p : ℝ => (2 : ℂ) * (v : ℂ) ^ 2 * (p : ℂ) *
      (massiveDiracRadialDenominator v p energy mass)⁻¹ ^ 2)
    (fun p => massiveDiracRadialDenominator_inv_hasDerivAt v p energy mass (hden p))
    hDerivativeCont hint hboundary

/-- Unconditional convergence of the *fixed-spectral-center* massive-Dirac
radial Fourier integral from a sufficiently large positive momentum.
The needed ultraviolet integrability and vanishing boundary term are
now derived from the quadratic denominator, rather than assumed. -/
theorem massiveDiracRadialFourierKernel_tendsto_atTop_uv
    (v c a : ℝ) (energy mass : ℂ) (hv : v ≠ 0) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0)
    (ha : max (1 : ℝ)
        (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2) ≤ a) :
    ∃ value : ℂ, Filter.Tendsto
      (fun b : ℝ => ∫ p in a..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹)
      Filter.atTop (nhds value) := by
  have hlimit :=
    tendsto_integral_massiveDiracRadialDenominator_inv_fourierKernel_of_conditions
      v c a energy mass hc hden
      (massiveDiracRadialFourierRemainder_integrableOn_uv
        v c a energy mass hv hden ha)
      (massiveDiracRadialDenominator_firstHarmonicBoundary_tendsto_zero
        v c energy mass hv)
  exact ⟨_, hlimit⟩

/-- The original radial Green resolvent integral from zero momentum has
a finite ultraviolet-cutoff limit at *fixed* nonvanishing complex
spectral denominator. The compact low-momentum contribution is
integrable by continuity; the large-momentum tail uses the proved
`p⁻²` remainder estimate. -/
theorem massiveDiracRadialFourierKernel_tendsto_atTop
    (v c : ℝ) (energy mass : ℂ) (hv : v ≠ 0) (hc : c ≠ 0)
    (hden : ∀ p : ℝ, massiveDiracRadialDenominator v p energy mass ≠ 0) :
    ∃ value : ℂ, Filter.Tendsto
      (fun b : ℝ => ∫ p in (0 : ℝ)..b,
        (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
          (massiveDiracRadialDenominator v p energy mass)⁻¹)
      Filter.atTop (nhds value) := by
  let cutoff : ℝ :=
    max 1 (2 * ‖energy ^ 2 - mass ^ 2‖ / v ^ 2)
  let f : ℝ → ℂ := fun p =>
    (p : ℂ) * polarFourierZerothAngularKernel (p * c) *
      (massiveDiracRadialDenominator v p energy mass)⁻¹
  obtain ⟨value, htail⟩ :=
    massiveDiracRadialFourierKernel_tendsto_atTop_uv
      v c cutoff energy mass hv hc hden le_rfl
  have hDcont : Continuous
      (fun p : ℝ => massiveDiracRadialDenominator v p energy mass) := by
    unfold massiveDiracRadialDenominator
    fun_prop
  have hInvCont : Continuous
      (fun p : ℝ => (massiveDiracRadialDenominator v p energy mass)⁻¹) :=
    hDcont.inv₀ hden
  have hKcont : Continuous
      (fun p : ℝ => polarFourierZerothAngularKernel (p * c)) :=
    continuous_polarFourierZerothAngularKernel.comp
      (continuous_id.mul continuous_const)
  have hf : Continuous f :=
    ((Complex.continuous_ofReal.comp continuous_id).mul hKcont).mul hInvCont
  have hleft : IntervalIntegrable f volume (0 : ℝ) cutoff :=
    hf.intervalIntegrable _ _
  have hsplit (b : ℝ) :
      (∫ p in (0 : ℝ)..b, f p) =
        (∫ p in (0 : ℝ)..cutoff, f p) +
        (∫ p in cutoff..b, f p) :=
    (intervalIntegral.integral_add_adjacent_intervals hleft
      (hf.intervalIntegrable cutoff b)).symm
  refine ⟨(∫ p in (0 : ℝ)..cutoff, f p) + value, ?_⟩
  have hconst : Filter.Tendsto
      (fun _ : ℝ => ∫ p in (0 : ℝ)..cutoff, f p)
      Filter.atTop (nhds (∫ p in (0 : ℝ)..cutoff, f p)) :=
    tendsto_const_nhds
  have hsum := hconst.add htail
  exact hsum.congr' (Filter.Eventually.of_forall fun b => (hsplit b).symm)

end

end QuantumTheory.Models.MassiveDirac
