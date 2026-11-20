import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Operator exponentials on eigenvectors

A bounded operator exponential acts on any eigenvector through the scalar
exponential of its eigenvalue. No eigenbasis or finite-dimensionality is needed.
-/

namespace NormedSpace
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- Evaluate the exponential of a bounded complex-linear operator on an eigenvector. -/
theorem exp_apply_of_eigenvector (T : H →L[ℂ] H) (v : H) (c : ℂ)
    (heigen : T v = c • v) :
    (NormedSpace.exp T) v = (NormedSpace.exp c) • v := by
  have hpow (n : ℕ) : (T ^ n) v = c ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        simp only [mul_apply_eq_comp, ih, map_smul, heigen, smul_smul]
        congr 1
        ring
  let eval : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H v
  let span : ℂ →L[ℂ] H := ContinuousLinearMap.toSpanSingleton ℂ v
  have hop := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T).map
    eval eval.continuous
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).map
    span span.continuous
  have hterms :
      (eval ∘ fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • T ^ n) =
        (span ∘ fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • c ^ n) := by
    funext n
    change ((Nat.factorial n : ℂ)⁻¹) • ((T ^ n) v) =
      (((Nat.factorial n : ℂ)⁻¹) * c ^ n) • v
    rw [hpow, smul_smul]
  rw [hterms] at hop
  simpa [eval, span] using hop.unique hscalar

end
end NormedSpace
