import LeanCondensedMatter.SecondQuantization.Common.Perturbation.InfiniteDyson

set_option linter.style.header false

/-!
# Continuity of finite-order Dyson coefficients on arbitrary configuration spaces

At every fixed Dyson order and basis input, the reachable support is finite.  This lets us expand
an interaction-picture action over a fixed finite set, so the usual scalar continuity argument for
the Dyson primitive does not require a finite ambient configuration type.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- Applying an algebraic-Fock linear map to a vector supported in `S` is a finite matrix-column
sum over `S`. -/
theorem linearMap_apply_eq_finsetSum_of_support_subset
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (x : AlgebraicFock Config) (S : Finset Config) (hx : x.support ⊆ S) (m : Config) :
    A x m = ∑ k ∈ S, matrixCoeff A m k * x k := by
  classical
  calc
    A x m = A (x.sum Finsupp.single) m := by rw [Finsupp.sum_single]
    _ = (x.sum fun k c => A (Finsupp.single k c)) m := by
      rw [map_finsuppSum]
    _ = x.sum (fun k c => A (Finsupp.single k c) m) := by
      rw [Finsupp.sum_apply]
    _ = ∑ k ∈ S, A (Finsupp.single k (x k)) m := by
      rw [Finsupp.sum_of_support_subset x hx]
      intro k _
      simp
    _ = ∑ k ∈ S, matrixCoeff A m k * x k := by
      apply Finset.sum_congr rfl
      intro k _
      have hsingle : (Finsupp.single k (x k) : AlgebraicFock Config) =
          x k • basisState k := (Finsupp.smul_single_one k (x k)).symm
      rw [hsingle, map_smul, Finsupp.smul_apply]
      rfl

/-- Every basis matrix coordinate of the arbitrary-configuration finite-order Dyson recursion is
continuous in imaginary time. -/
theorem continuous_infiniteDysonCoeff_basisState_apply (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ∀ order m n : Config,
      Continuous (fun τ : ℝ => infiniteDysonCoeff energy V order τ (basisState n) m) := by
  intro order
  induction order with
  | zero =>
      intro m n
      simp only [infiniteDysonCoeff_zero, LinearMap.id_apply]
      exact continuous_const
  | succ order ih =>
      intro m n
      simp only [infiniteDysonCoeff_succ_basisState_apply]
      have hcont : Continuous (fun σ : ℝ =>
          interactionPicture energy V σ
            (infiniteDysonCoeff energy V order σ (basisState n)) m) := by
        let S := reachableSupport V order n
        have heq : (fun σ : ℝ => interactionPicture energy V σ
              (infiniteDysonCoeff energy V order σ (basisState n)) m) =
            (fun σ : ℝ => ∑ k ∈ S,
              matrixCoeff (interactionPicture energy V σ) m k *
                infiniteDysonCoeff energy V order σ (basisState n) k) := by
          funext σ
          exact linearMap_apply_eq_finsetSum_of_support_subset
            (interactionPicture energy V σ)
            (infiniteDysonCoeff energy V order σ (basisState n)) S
            (support_infiniteDysonCoeff_basisState_subset_reachableSupport
              energy V order σ n) m
        rw [heq]
        exact continuous_finsetSum S fun k _ =>
          (continuous_matrixCoeff_interactionPicture energy V m k).mul (ih k n)
      exact (intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).neg

/-- Every matrix coefficient of the arbitrary-configuration finite-order Dyson recursion is
continuous in imaginary time. -/
theorem continuous_matrixCoeff_infiniteDysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (m n : Config) :
    Continuous (fun τ : ℝ => matrixCoeff (infiniteDysonCoeff energy V order τ) m n) := by
  change Continuous (fun τ : ℝ => infiniteDysonCoeff energy V order τ (basisState n) m)
  exact continuous_infiniteDysonCoeff_basisState_apply energy V order m n

/-- Every matrix coefficient of the arbitrary-configuration finite-order Dyson recursion is
interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_infiniteDysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ)
    (m n : Config) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => matrixCoeff (infiniteDysonCoeff energy V order τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_infiniteDysonCoeff energy V order m n).intervalIntegrable a b

end Common
end SecondQuantization
