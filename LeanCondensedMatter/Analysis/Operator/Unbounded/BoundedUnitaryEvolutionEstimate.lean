import LeanCondensedMatter.Analysis.Operator.Unbounded.BoundedUnitaryEvolutionVectorwise
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Norm estimates for bounded unitary evolution

For a bounded self-adjoint generator `B`, the evolution `exp (-i t B)` preserves vector norms.
Combining this with the vectorwise differential equation and the mean-value inequality gives the
basic displacement estimate `‖U_B(t)x - x‖ ≤ |t| ‖B x‖`.  This is the analytic estimate used to
show that the bounded Stone approximants form a strongly Cauchy family.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded self-adjoint exponential preserves the norm of every vector. -/
theorem boundedUnitaryEvolution_apply_norm
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (t : ℝ) (x : H) :
    ‖boundedUnitaryEvolution B t x‖ = ‖x‖ := by
  let U : H →L[ℂ] H := boundedUnitaryEvolution B t
  have hunit : star U * U = 1 := by
    simpa [U] using boundedUnitaryEvolution_star_mul B hB t
  have huux : ContinuousLinearMap.adjoint U (U x) = x := by
    have happly := congrArg (fun T : H →L[ℂ] H => T x) hunit
    simpa [ContinuousLinearMap.star_eq_adjoint] using happly
  have hsq_complex : ((‖U x‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    calc
      ((‖U x‖ ^ 2 : ℝ) : ℂ) = inner ℂ (U x) (U x) :=
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (U x)).symm
      _ = inner ℂ (ContinuousLinearMap.adjoint U (U x)) x :=
        (ContinuousLinearMap.adjoint_inner_left U x (U x)).symm
      _ = inner ℂ x x := by rw [huux]
      _ = ((‖x‖ ^ 2 : ℝ) : ℂ) := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  have hsq : ‖U x‖ ^ 2 = ‖x‖ ^ 2 := Complex.ofReal_injective hsq_complex
  nlinarith [norm_nonneg (U x), norm_nonneg x]

/-- The vectorwise derivative of a bounded self-adjoint evolution has constant norm `‖B x‖`. -/
theorem norm_boundedUnitaryEvolution_apply_deriv
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (t : ℝ) (x : H) :
    ‖((boundedUnitaryEvolution B t * ((-I : ℂ) • B)) x)‖ = ‖B x‖ := by
  change ‖boundedUnitaryEvolution B t (((-I : ℂ) • B) x)‖ = ‖B x‖
  rw [boundedUnitaryEvolution_apply_norm B hB t]
  change ‖(-I : ℂ) • B x‖ = ‖B x‖
  rw [norm_smul]
  simp

/-- The displacement under bounded self-adjoint evolution is controlled by the generator on the
initial vector. -/
theorem norm_boundedUnitaryEvolution_apply_sub_le
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (t : ℝ) (x : H) :
    ‖boundedUnitaryEvolution B t x - x‖ ≤ ‖B x‖ * |t| := by
  have hderiv : ∀ τ ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun s : ℝ => boundedUnitaryEvolution B s x)
        ((boundedUnitaryEvolution B τ * ((-I : ℂ) • B)) x) Set.univ τ := by
    intro τ _
    exact (boundedUnitaryEvolution_apply_hasDerivAt B τ x).hasDerivWithinAt
  have hbound : ∀ τ ∈ (Set.univ : Set ℝ),
      ‖((boundedUnitaryEvolution B τ * ((-I : ℂ) • B)) x)‖ ≤ ‖B x‖ := by
    intro τ _
    exact le_of_eq (norm_boundedUnitaryEvolution_apply_deriv B hB τ x)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => boundedUnitaryEvolution B s x)
    (f' := fun τ : ℝ => (boundedUnitaryEvolution B τ * ((-I : ℂ) • B)) x)
    (s := Set.univ) (x := (0 : ℝ)) (y := t)
    hderiv hbound convex_univ (Set.mem_univ 0) (Set.mem_univ t)
  simpa using hmv

end

end LinearPMap
