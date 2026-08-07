import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Bounded multiplication operators on one-dimensional `L²`

This module starts the analytic `L²` boundary of the continuum continuity program. A multiplier
`f ∈ L∞(ℝ, ℂ)` acts on a wavefunction `ψ ∈ L²(ℝ, ℂ)` by pointwise multiplication. Hölder's
inequality gives a bounded operator on `L²` with norm bounded by `‖f‖`.

The construction is deliberately limited to bounded multipliers. The kinetic Schrödinger operator
and other genuinely unbounded operators require an explicit domain and are not introduced here.
-/

namespace QuantumTheory
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- Complex one-dimensional square-integrable wavefunctions. -/
abbrev ContinuumL2Wavefunction1D := ↥(Lp ℂ 2 (volume : Measure ℝ))

/-- Essentially bounded complex multipliers on one-dimensional space. -/
abbrev ContinuumLInfMultiplier1D := ↥(Lp ℂ ∞ (volume : Measure ℝ))

/-- Multiplication by an `L∞` function as a bounded operator on `L²`.

Pointwise this is `ψ ↦ f ψ`. The construction uses the heterogeneous `Lp` multiplication from
Mathlib's Hölder layer with exponents `∞`, `2`, and `2`. -/
noncomputable def l2MultiplicationOperator1D
    (f : ContinuumLInfMultiplier1D) :
    ContinuumL2Wavefunction1D →L[ℂ] ContinuumL2Wavefunction1D :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (f • ψ : ContinuumL2Wavefunction1D)
      map_add' := by
        intro ψ φ
        exact Lp.add_smul f ψ φ
      map_smul' := by
        intro c ψ
        exact (Lp.smul_comm c f ψ).symm }
    ‖f‖
    (fun ψ => Lp.norm_smul_le f ψ)

@[simp]
theorem l2MultiplicationOperator1D_apply
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    l2MultiplicationOperator1D f ψ = (f • ψ : ContinuumL2Wavefunction1D) :=
  rfl

/-- The multiplication operator has operator norm at most the `L∞` norm of its multiplier. -/
theorem l2MultiplicationOperator1D_norm_le
    (f : ContinuumLInfMultiplier1D) :
    ‖l2MultiplicationOperator1D f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg f
  · intro ψ
    exact Lp.norm_smul_le f ψ

/-- The bounded `L²` multiplication operator agrees almost everywhere with pointwise
multiplication of representatives. -/
theorem l2MultiplicationOperator1D_coeFn
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    (l2MultiplicationOperator1D f ψ : ℝ → ℂ) =ᵐ[volume]
      fun x => f x * ψ x := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) f ψ] with x hx
  simpa using hx

/-- The `L²` expectation of a bounded multiplication operator is the Lebesgue integral of the
pointwise inner-product density. -/
theorem inner_l2MultiplicationOperator1D_eq_integral
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    inner ℂ ψ (l2MultiplicationOperator1D f ψ) =
      ∫ x : ℝ, inner ℂ (ψ x) (f x * ψ x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2MultiplicationOperator1D_coeFn f ψ] with x hx
  rw [hx]

end
end Continuum
end QuantumTheory
