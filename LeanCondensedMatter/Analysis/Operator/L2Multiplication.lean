import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Bounded multiplication operators on complex `L²`

This module owns the measure-space-independent multiplication-operator infrastructure used by the
continuum quantum-mechanics and second-quantization layers. For any measure `μ`, an essentially
bounded complex function acts on `L²(μ, ℂ)` by pointwise multiplication, and Hölder's inequality
makes this action a bounded operator.

Real-valued essentially bounded functions give symmetric multiplication operators. Only bounded
multipliers are treated here; genuinely unbounded multiplication operators require explicit domains
and belong to the unbounded-operator layer.
-/

namespace L2Multiplication

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

variable {α : Type*} [MeasurableSpace α]

/-- Complex square-integrable functions for a measure `μ`. -/
abbrev ComplexL2 (μ : Measure α) := ↥(Lp ℂ 2 μ)

/-- Essentially bounded complex multipliers for a measure `μ`. -/
abbrev ComplexLInf (μ : Measure α) := ↥(Lp ℂ ∞ μ)

/-- Multiplication by an `L∞` function as a bounded operator on `L²`.

Pointwise this is `ψ ↦ f ψ`. The construction uses Mathlib's heterogeneous `Lp` multiplication
with exponents `∞`, `2`, and `2`. -/
noncomputable def multiplicationOperator
    (μ : Measure α) (f : ComplexLInf μ) : ComplexL2 μ →L[ℂ] ComplexL2 μ :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (f • ψ : ComplexL2 μ)
      map_add' := by
        intro ψ φ
        exact Lp.add_smul f ψ φ
      map_smul' := by
        intro c ψ
        exact (Lp.smul_comm c f ψ).symm }
    ‖f‖
    (fun ψ => Lp.norm_smul_le f ψ)

@[simp]
theorem multiplicationOperator_apply
    (μ : Measure α) (f : ComplexLInf μ) (ψ : ComplexL2 μ) :
    multiplicationOperator μ f ψ = (f • ψ : ComplexL2 μ) :=
  rfl

/-- The multiplication operator has operator norm at most the `L∞` norm of its multiplier. -/
theorem multiplicationOperator_norm_le
    (μ : Measure α) (f : ComplexLInf μ) :
    ‖multiplicationOperator μ f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg f
  · intro ψ
    exact Lp.norm_smul_le f ψ

/-- The bounded multiplication operator agrees almost everywhere with pointwise multiplication of
representatives. -/
private theorem multiplicationOperator_coeFn
    (μ : Measure α) (f : ComplexLInf μ) (ψ : ComplexL2 μ) :
    (multiplicationOperator μ f ψ : α → ℂ) =ᵐ[μ]
      fun x => f x * ψ x := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) f ψ] with x hx
  simpa using hx

/-- The `L²` expectation of a bounded multiplication operator is the integral of the pointwise
inner-product density. -/
theorem inner_multiplicationOperator_eq_integral
    (μ : Measure α) (f : ComplexLInf μ) (ψ : ComplexL2 μ) :
    inner ℂ ψ (multiplicationOperator μ f ψ) =
      ∫ x, inner ℂ (ψ x) (f x * ψ x) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplicationOperator_coeFn μ f ψ] with x hx
  rw [hx]

/-- A real essentially bounded function, embedded into `ℂ`, as an `L∞` multiplier. -/
noncomputable def realMultiplier
    (μ : Measure α) (f : α → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ μ) :
    ComplexLInf μ :=
  hf.toLp (fun x => (f x : ℂ))

/-- The `L∞` representative chosen for a real bounded function agrees almost everywhere with its
pointwise complex embedding. -/
theorem realMultiplier_coeFn
    (μ : Measure α) (f : α → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ μ) :
    (realMultiplier μ f hf : α → ℂ) =ᵐ[μ]
      fun x => (f x : ℂ) := by
  exact hf.coeFn_toLp

private theorem inner_real_mul_left_eq_inner_real_mul_right
    (r : ℝ) (z w : ℂ) :
    inner ℂ ((r : ℂ) * z) w = inner ℂ z ((r : ℂ) * w) := by
  simp [RCLike.inner_apply, mul_assoc, mul_comm]

/-- Multiplication by a bounded real function is symmetric on complex `L²`. -/
theorem realMultiplicationOperator_symmetric
    (μ : Measure α) (f : α → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ μ)
    (ψ φ : ComplexL2 μ) :
    inner ℂ (multiplicationOperator μ (realMultiplier μ f hf) ψ) φ =
      inner ℂ ψ (multiplicationOperator μ (realMultiplier μ f hf) φ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
      [multiplicationOperator_coeFn μ (realMultiplier μ f hf) ψ,
       multiplicationOperator_coeFn μ (realMultiplier μ f hf) φ,
       realMultiplier_coeFn μ f hf] with x hψ hφ hf'
  rw [hψ, hφ, hf']
  exact inner_real_mul_left_eq_inner_real_mul_right (f x) (ψ x) (φ x)

/-- Multiplication on complex `L²` depends complex-linearly on the `L∞` multiplier, after
forgetting continuity of each individual operator. -/
noncomputable def multiplicationLinear (μ : Measure α) :
    ComplexLInf μ →ₗ[ℂ] (ComplexL2 μ →ₗ[ℂ] ComplexL2 μ) where
  toFun := fun f => (multiplicationOperator μ f).toLinearMap
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro ψ
    change (f + g) • ψ = f • ψ + g • ψ
    exact Lp.smul_add f g ψ
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro ψ
    change (c • f) • ψ = c • (f • ψ)
    exact Lp.smul_assoc c f ψ

@[simp]
theorem multiplicationLinear_apply
    (μ : Measure α) (f : ComplexLInf μ) (ψ : ComplexL2 μ) :
    multiplicationLinear μ f ψ = multiplicationOperator μ f ψ :=
  rfl

end
end L2Multiplication
