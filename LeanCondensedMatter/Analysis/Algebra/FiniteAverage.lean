import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
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

section ScalarWeights

variable {R Ω : Type*} [CommRing R] [Fintype Ω] (w : Ω → R)

/-- A finite scalar-weighted sum of module-valued families. -/
noncomputable def finiteWeightedSum {E : Type*} [AddCommMonoid E] [Module R E] :
    (Ω → E) →ₗ[R] E where
  toFun response := ∑ ω, w ω • response ω
  map_add' left right := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' c response := by simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp] theorem finiteWeightedSum_apply {E : Type*} [AddCommMonoid E] [Module R E]
    (response : Ω → E) : finiteWeightedSum w response = ∑ ω, w ω • response ω := rfl

/-- Every linear map commutes with a finite weighted sum. -/
theorem map_finiteWeightedSum {E F : Type*}
    [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
    (f : E →ₗ[R] F) (response : Ω → E) :
    f (finiteWeightedSum w response) = finiteWeightedSum w (fun ω => f (response ω)) := by
  change f (∑ ω, w ω • response ω) =
    ∑ ω, w ω • f (response ω)
  simp only [map_sum, map_smul]

/-- Normalization makes the finite weighted sum fix constant families. -/
theorem finiteWeightedSum_const {E : Type*} [AddCommMonoid E] [Module R E] (hweight : ∑ ω, w ω = 1) (value : E) :
    finiteWeightedSum w (fun _ => value) = value := by
  change (∑ ω, w ω • value) = value
  rw [← Finset.sum_smul]
  rw [hweight, one_smul]

/-- A normalized finite average of a bilinear pairing decomposes into the pairing of
the means and the pairing of the centered fluctuations. The modules need no norm,
multiplication, or inner product. -/
theorem finiteWeightedSum_bilinear_eq_mean_add_centered {E F G : Type*}
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (hweight : ∑ ω, w ω = 1)
    (B : E →ₗ[R] F →ₗ[R] G) (left : Ω → E) (right : Ω → F) :
    finiteWeightedSum w (fun ω => B (left ω) (right ω)) =
      B (finiteWeightedSum w left) (finiteWeightedSum w right) +
        finiteWeightedSum w (fun ω =>
          B (left ω - finiteWeightedSum w left) (right ω - finiteWeightedSum w right)) := by
  let x := finiteWeightedSum w left
  let y := finiteWeightedSum w right
  have hright : finiteWeightedSum w (fun ω => B (left ω) y) = B x y :=
    (map_finiteWeightedSum w (B.flip y) left).symm
  have hleft : finiteWeightedSum w (fun ω => B x (right ω)) = B x y :=
    (map_finiteWeightedSum w (B x) right).symm
  have hcenter :
      (fun ω => B (left ω - x) (right ω - y)) =
        (fun ω => B (left ω) (right ω)) - (fun ω => B (left ω) y) -
          (fun ω => B x (right ω)) + (fun _ => B x y) := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, LinearMap.sub_apply]
    abel
  change finiteWeightedSum w (fun ω => B (left ω) (right ω)) =
    B x y + finiteWeightedSum w (fun ω => B (left ω - x) (right ω - y))
  rw [hcenter, map_add, map_sub, map_sub, hright, hleft, finiteWeightedSum_const w hweight]
  abel

end ScalarWeights

variable {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)

/-- A finite real-weighted sum of complex-module-valued families. -/
noncomputable def finiteWeightedAverage {E : Type*} [AddCommMonoid E] [Module ℂ E] :
    (Ω → E) →ₗ[ℂ] E :=
  finiteWeightedSum (fun ω => (w ω : ℂ))

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

/-- A weighted sandwich by scalar multiples of the identity is scalar multiplication
by the weighted square of those scalars. Neither normalized nor positive weights are needed. -/
theorem finiteWeightedAverage_sandwich_scalar {A : Type*} [Ring A] [Algebra ℂ A]
    (u : Ω → ℂ) (x : A) :
    finiteWeightedAverage w (fun ω => (u ω • (1 : A)) * x * (u ω • (1 : A))) =
      finiteWeightedAverage w (fun ω => u ω ^ 2) • x := by
  change (∑ ω, (w ω : ℂ) • ((u ω • (1 : A)) * x * (u ω • (1 : A)))) =
    (∑ ω, (w ω : ℂ) • (u ω ^ 2)) • x
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, pow_two,
    smul_eq_mul]

/-- Right multiplication by a commuting element passes through a weighted sandwich. -/
theorem finiteWeightedAverage_sandwich_mul {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Ω → A) (x y : A) (h : ∀ ω, Commute (v ω) y) :
    finiteWeightedAverage w (fun ω => v ω * x * v ω) * y =
      finiteWeightedAverage w (fun ω => v ω * (x * y) * v ω) := by
  change (∑ ω, (w ω : ℂ) • (v ω * x * v ω)) * y =
    ∑ ω, (w ω : ℂ) • (v ω * (x * y) * v ω)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_mul_assoc]
  apply congrArg (fun a : A => (w ω : ℂ) • a)
  simpa only [mul_assoc] using congrArg (fun a : A => v ω * x * a) (h ω).eq

/-- Left multiplication by a commuting element passes through a weighted sandwich. -/
theorem mul_finiteWeightedAverage_sandwich {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Ω → A) (x y : A) (h : ∀ ω, Commute (v ω) y) :
    y * finiteWeightedAverage w (fun ω => v ω * x * v ω) =
      finiteWeightedAverage w (fun ω => v ω * (y * x) * v ω) := by
  change y * (∑ ω, (w ω : ℂ) • (v ω * x * v ω)) =
    ∑ ω, (w ω : ℂ) • (v ω * (y * x) * v ω)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [mul_smul_comm]
  apply congrArg (fun a : A => (w ω : ℂ) • a)
  simpa only [mul_assoc] using congrArg (fun a : A => a * x * v ω) (h ω).eq.symm

end

end LinearMap
