import LeanCondensedMatter.Transport.Analysis.PolarFourier
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Differentiation of finite-cutoff radial Fourier integrals

The first-harmonic angular kernel is uniformly bounded by the angular
integration interval. This permits differentiation with respect to a signed
real-space radius through a **finite** radial momentum integral for any
continuous complex radial weight. The argument retains the momentum cutoff
and the Fourier length scale; no infinite-radius, infinite-momentum,
broadening, or disorder limit is involved.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- The first angular Fourier harmonic is uniformly bounded by the
length of the full angular interval, independently of its argument. -/
theorem polarFourierFirstCosineAngularKernel_norm_le (z : ℝ) :
    ‖polarFourierFirstCosineAngularKernel z‖ ≤ 2 * Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := (1 : ℝ))
    (f := fun θ : ℝ =>
      polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) (by
      intro θ _
      have hphase : ‖polarFourierRadialPhase z θ‖ = 1 := by
        simp [polarFourierRadialPhase, Complex.norm_exp, Complex.mul_re]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hphase, one_mul]
      exact Real.abs_cos_le_one θ)
  simpa only [polarFourierFirstCosineAngularKernel, one_mul, sub_zero,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
    using h

/-- The finite-cutoff zeroth-harmonic integral is differentiable in the
real-space radius. The derivative is exactly its first cosine harmonic,
including the momentum-to-radius scale factor. In particular, this
theorem does not interchange a derivative with an improper integral. -/
theorem hasDerivAt_integral_polarFourierZerothAngularKernel
    (weight : ℝ → ℂ) (hweight : Continuous weight)
    (pMax hbar radius : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ p in (0 : ℝ)..pMax,
        weight p * polarFourierZerothAngularKernel (p * r / hbar))
      (∫ p in (0 : ℝ)..pMax,
        weight p * (Complex.I * ((p / hbar : ℝ) : ℂ) *
          polarFourierFirstCosineAngularKernel (p * radius / hbar)))
      radius := by
  let F : ℝ → ℝ → ℂ := fun r p =>
    weight p * polarFourierZerothAngularKernel (p * r / hbar)
  let F' : ℝ → ℝ → ℂ := fun r p =>
    weight p * (Complex.I * ((p / hbar : ℝ) : ℂ) *
      polarFourierFirstCosineAngularKernel (p * r / hbar))
  let bound : ℝ → ℝ := fun p =>
    (‖weight p‖ * |p / hbar|) * (2 * Real.pi)
  have hc0 : Continuous polarFourierZerothAngularKernel :=
    continuous_iff_continuousAt.mpr fun z =>
      (polarFourierZerothAngularKernel_hasDerivAt z).continuousAt
  have hc1 : Continuous polarFourierFirstCosineAngularKernel :=
    continuous_iff_continuousAt.mpr fun z =>
      (polarFourierFirstCosineAngularKernel_hasDerivAt z).continuousAt
  have hderiv (r p : ℝ) :
      HasDerivAt (fun t : ℝ => F t p) (F' r p) r := by
    have harg : HasDerivAt (fun t : ℝ => p * t / hbar) (p / hbar) r := by
      convert (((hasDerivAt_id r).const_mul p).div_const hbar) using 1 <;>
        first | rfl | ring
    have hk := (polarFourierZerothAngularKernel_hasDerivAt
      (p * r / hbar)).comp r harg
    have h := hk.const_mul (weight p)
    convert h using 1
    · rfl
    · dsimp [F']
      push_cast
      ring
  have hcont (r : ℝ) : Continuous (F r) := by
    dsimp [F]
    exact hweight.mul (hc0.comp (by fun_prop))
  have hcont' (r : ℝ) : Continuous (F' r) := by
    dsimp [F']
    exact hweight.mul ((continuous_const.mul
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul
        (hc1.comp (by fun_prop)))))
  have hbound (r p : ℝ) : ‖F' r p‖ ≤ bound p := by
    have hn : ‖F' r p‖ =
        (‖weight p‖ * |p / hbar|) *
          ‖polarFourierFirstCosineAngularKernel (p * r / hbar)‖ := by
      dsimp [F']
      simp only [norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, one_mul]
      ring
    rw [hn]
    exact mul_le_mul_of_nonneg_left
      (polarFourierFirstCosineAngularKernel_norm_le _) (by positivity)
  have hboundCont : Continuous bound := by
    dsimp [bound]
    fun_prop
  have hmain :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound)
      (s := Set.univ) (x₀ := radius) (a := (0 : ℝ)) (b := pMax)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun r => (hcont r).aestronglyMeasurable)
      ((hcont radius).intervalIntegrable _ _)
      ((hcont' radius).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p _ r _ => hbound r p)
      (hboundCont.intervalIntegrable _ _)
      (Filter.Eventually.of_forall fun p _ r _ => hderiv r p)).2
  exact hmain

end

end Transport
end QuantumTheory
