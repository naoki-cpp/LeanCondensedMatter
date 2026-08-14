import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Bounded multiplication operators on `L²(ℝ, ℂ)`

This module owns the analysis-level multiplication-operator infrastructure on the real line. An
essentially bounded complex function acts on `L²(ℝ, ℂ)` by pointwise multiplication, and Hölder's
inequality makes this action a bounded operator.

The construction is independent of quantum mechanics and second quantization. Downstream physics
layers may specialize the same canonical `L²` and `L∞` realization without depending on one another.

Only bounded multipliers are treated here. Genuinely unbounded operators require explicit domains
and belong to the unbounded-operator layer.
-/

namespace L2MultiplicationRealLine

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- Complex square-integrable functions on the real line. -/
abbrev ComplexL2 := ↥(Lp ℂ 2 (volume : Measure ℝ))

/-- Essentially bounded complex multipliers on the real line. -/
abbrev ComplexLInf := ↥(Lp ℂ ∞ (volume : Measure ℝ))

/-- Multiplication by an `L∞` function as a bounded operator on `L²`.

Pointwise this is `ψ ↦ f ψ`. The construction uses Mathlib's heterogeneous `Lp` multiplication
with exponents `∞`, `2`, and `2`. -/
noncomputable def multiplicationOperator
    (f : ComplexLInf) : ComplexL2 →L[ℂ] ComplexL2 :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (f • ψ : ComplexL2)
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
    (f : ComplexLInf) (ψ : ComplexL2) :
    multiplicationOperator f ψ = (f • ψ : ComplexL2) :=
  rfl

/-- The multiplication operator has operator norm at most the `L∞` norm of its multiplier. -/
theorem multiplicationOperator_norm_le (f : ComplexLInf) :
    ‖multiplicationOperator f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg f
  · intro ψ
    exact Lp.norm_smul_le f ψ

/-- The bounded multiplication operator agrees almost everywhere with pointwise multiplication of
representatives. -/
theorem multiplicationOperator_coeFn
    (f : ComplexLInf) (ψ : ComplexL2) :
    (multiplicationOperator f ψ : ℝ → ℂ) =ᵐ[volume]
      fun x => f x * ψ x := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) f ψ] with x hx
  simpa using hx

/-- The `L²` expectation of a bounded multiplication operator is the Lebesgue integral of the
pointwise inner-product density. -/
theorem inner_multiplicationOperator_eq_integral
    (f : ComplexLInf) (ψ : ComplexL2) :
    inner ℂ ψ (multiplicationOperator f ψ) =
      ∫ x : ℝ, inner ℂ (ψ x) (f x * ψ x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplicationOperator_coeFn f ψ] with x hx
  rw [hx]

/-- A real essentially bounded function, embedded into `ℂ`, as an `L∞` multiplier. -/
noncomputable def realMultiplier
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    ComplexLInf :=
  hf.toLp (fun x => (f x : ℂ))

/-- The `L∞` representative chosen for a real bounded function agrees almost everywhere with its
pointwise complex embedding. -/
theorem realMultiplier_coeFn
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    (realMultiplier f hf : ℝ → ℂ) =ᵐ[volume]
      fun x => (f x : ℂ) := by
  exact hf.coeFn_toLp

private theorem inner_real_mul_left_eq_inner_real_mul_right
    (r : ℝ) (z w : ℂ) :
    inner ℂ ((r : ℂ) * z) w = inner ℂ z ((r : ℂ) * w) := by
  simp [RCLike.inner_apply, mul_assoc, mul_comm]

/-- Multiplication by a bounded real function is symmetric on `L²(ℝ, ℂ)`. -/
theorem realMultiplicationOperator_symmetric
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ))
    (ψ φ : ComplexL2) :
    inner ℂ (multiplicationOperator (realMultiplier f hf) ψ) φ =
      inner ℂ ψ (multiplicationOperator (realMultiplier f hf) φ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
      [multiplicationOperator_coeFn (realMultiplier f hf) ψ,
       multiplicationOperator_coeFn (realMultiplier f hf) φ,
       realMultiplier_coeFn f hf] with x hψ hφ hf'
  rw [hψ, hφ, hf']
  exact inner_real_mul_left_eq_inner_real_mul_right (f x) (ψ x) (φ x)

/-- A bounded real multiplication operator, viewed as a partial operator with full domain, is a
formal adjoint of itself. -/
theorem realMultiplicationOperator_isFormalAdjoint
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    let M := multiplicationOperator (realMultiplier f hf)
    (M.toPMap ⊤).IsFormalAdjoint (M.toPMap ⊤) := by
  dsimp
  intro ψ φ
  simpa using realMultiplicationOperator_symmetric f hf
    (ψ : ComplexL2) (φ : ComplexL2)

end
end L2MultiplicationRealLine
