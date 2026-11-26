import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Finite weighted averages

The linear weighted sum and its normalized bilinear decomposition are independent
of Hamiltonians, operator multiplication and positivity of the weights.
-/

namespace LinearMap

open scoped BigOperators

noncomputable section

variable {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)

/-- A finite real-weighted sum of complex-module-valued families. -/
noncomputable def finiteWeightedAverage {E : Type*} [AddCommMonoid E] [Module ℂ E] :
    (Ω → E) →ₗ[ℂ] E where
  toFun response := ∑ ω, (w ω : ℂ) • response ω
  map_add' left right := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' c response := by simp [Finset.smul_sum, smul_smul, mul_comm]

/-- Every complex-linear map commutes with a finite weighted sum. -/
theorem map_finiteWeightedAverage {E F : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
    (f : E →ₗ[ℂ] F) (response : Ω → E) :
    f (finiteWeightedAverage w response) = finiteWeightedAverage w (fun ω => f (response ω)) := by
  change f (∑ ω, (w ω : ℂ) • response ω) =
    ∑ ω, (w ω : ℂ) • f (response ω)
  simp only [map_sum, map_smul]

/-- Normalization makes the finite weighted sum fix constant families. -/
theorem finiteWeightedAverage_const {E : Type*} [AddCommMonoid E] [Module ℂ E] (hweight : ∑ ω, w ω = 1) (value : E) :
    finiteWeightedAverage w (fun _ => value) = value := by
  change (∑ ω, (w ω : ℂ) • value) = value
  rw [← Finset.sum_smul]
  have hsum : (∑ ω, (w ω : ℂ)) = 1 := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hweight
  simp [hsum]

/-- A normalized finite average of a bilinear pairing decomposes into the pairing of
the means and the pairing of the centered fluctuations. The modules need no norm,
multiplication, or inner product. -/
theorem finiteWeightedAverage_bilinear_eq_mean_add_centered {E F G : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G]
    (hweight : ∑ ω, w ω = 1)
    (B : E →ₗ[ℂ] F →ₗ[ℂ] G) (left : Ω → E) (right : Ω → F) :
    finiteWeightedAverage w (fun ω => B (left ω) (right ω)) =
      B (finiteWeightedAverage w left) (finiteWeightedAverage w right) +
        finiteWeightedAverage w (fun ω =>
          B (left ω - finiteWeightedAverage w left) (right ω - finiteWeightedAverage w right)) := by
  let x := finiteWeightedAverage w left
  let y := finiteWeightedAverage w right
  have hright : finiteWeightedAverage w (fun ω => B (left ω) y) = B x y :=
    (map_finiteWeightedAverage w (B.flip y) left).symm
  have hleft : finiteWeightedAverage w (fun ω => B x (right ω)) = B x y :=
    (map_finiteWeightedAverage w (B x) right).symm
  have hcenter :
      (fun ω => B (left ω - x) (right ω - y)) =
        (fun ω => B (left ω) (right ω)) - (fun ω => B (left ω) y) -
          (fun ω => B x (right ω)) + (fun _ => B x y) := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, LinearMap.sub_apply]
    abel
  change finiteWeightedAverage w (fun ω => B (left ω) (right ω)) =
    B x y + finiteWeightedAverage w (fun ω => B (left ω - x) (right ω - y))
  rw [hcenter, map_add, map_sub, map_sub, hright, hleft, finiteWeightedAverage_const w hweight]
  abel

/-- A pointwise norm bound passes to a nonnegative weighted finite sum.
Normalization of the weights is not needed. -/
theorem norm_finiteWeightedAverage_le_sum_of_forall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hw : ∀ ω, 0 ≤ w ω) (response : Ω → E) (bound : Ω → ℝ)
    (hpoint : ∀ ω, ‖response ω‖ ≤ bound ω) :
    ‖finiteWeightedAverage w response‖ ≤ ∑ ω, w ω * bound ω := by
  calc
    ‖finiteWeightedAverage w response‖ =
        ‖∑ ω, (w ω : ℂ) • response ω‖ := rfl
    _ ≤ ∑ ω, ‖(w ω : ℂ) • response ω‖ := norm_sum_le _ _
    _ = ∑ ω, w ω * ‖response ω‖ := by
      apply Finset.sum_congr rfl
      intro ω _
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw ω)]
    _ ≤ ∑ ω, w ω * bound ω :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω) (hw ω)

/-- A normalized nonnegative finite weighted average preserves uniform norm bounds. -/
theorem norm_finiteWeightedAverage_le_of_forall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (response : Ω → E) (bound : ℝ) (hpoint : ∀ ω, ‖response ω‖ ≤ bound) :
    ‖finiteWeightedAverage w response‖ ≤ bound := by
  calc
    _ ≤ ∑ ω, w ω * bound :=
      norm_finiteWeightedAverage_le_sum_of_forall w hw response (fun _ => bound) hpoint
    _ = bound := by rw [← Finset.sum_mul, hsum, one_mul]

end

end LinearMap
