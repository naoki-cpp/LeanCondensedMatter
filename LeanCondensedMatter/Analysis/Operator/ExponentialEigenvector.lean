import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-! # Operator exponentials on eigenvectors

A bounded operator exponential acts on any eigenvector through the scalar
exponential of its eigenvalue. No eigenbasis or finite-dimensionality is needed.
-/

namespace NormedSpace
noncomputable section

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] [CompleteSpace H]

/-- Evaluate the exponential of a bounded real- or complex-linear operator on an eigenvector. -/
theorem exp_apply_of_eigenvector (T : H →L[𝕜] H) (v : H) (c : 𝕜)
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
  let eval : (H →L[𝕜] H) →L[𝕜] H := ContinuousLinearMap.apply 𝕜 H v
  let span : 𝕜 →L[𝕜] H := ContinuousLinearMap.toSpanSingleton 𝕜 v
  have hop := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) T).map
    eval eval.continuous
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) c).map
    span span.continuous
  have hterms :
      (eval ∘ fun n : ℕ => ((Nat.factorial n : 𝕜)⁻¹) • T ^ n) =
        (span ∘ fun n : ℕ => ((Nat.factorial n : 𝕜)⁻¹) • c ^ n) := by
    funext n
    change ((Nat.factorial n : 𝕜)⁻¹) • ((T ^ n) v) =
      (((Nat.factorial n : 𝕜)⁻¹) * c ^ n) • v
    rw [hpow, smul_smul]
  rw [hterms] at hop
  simpa [eval, span] using hop.unique hscalar

end
end NormedSpace
