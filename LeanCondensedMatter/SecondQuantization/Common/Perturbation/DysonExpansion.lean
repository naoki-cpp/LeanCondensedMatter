import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteSupportIntegral
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteOperatorIntegral

set_option linter.style.header false

/-!
# Finite-order Dyson coefficients

For a basis-diagonal free energy and an algebraic interaction, each finite Dyson order reaches only
finitely many configurations from any basis state. This file uses that reachable support to define
the statistics-independent interaction-picture recursion on an arbitrary configuration type,

`D₀(τ) = id`,  `Dₙ₊₁(τ) = -∫ σ in 0..τ, V_I(σ) ∘ Dₙ(σ)`.

The recursion is reconstructed coefficientwise and is therefore algebraic and finite-order. No
boundedness, completed-space Bochner integrability, convergence of the infinite Dyson series, or
identification with an operator exponential is asserted here. On finite configuration types, the
same canonical coefficients satisfy the previous finite operator-integral recursion.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

private noncomputable def dysonBasis (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ℕ → ℝ → Config → AlgebraicFock Config
  | 0, _, n => basisState n
  | order + 1, τ, n =>
      - finiteSupportIntervalIntegral (reachableSupport V (order + 1) n)
          (fun σ => interactionPicture energy V σ (dysonBasis energy V order σ n)) 0 τ

private theorem dysonBasis_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (n : Config) :
    dysonBasis energy V (order + 1) τ n =
      - finiteSupportIntervalIntegral (reachableSupport V (order + 1) n)
          (fun σ => interactionPicture energy V σ (dysonBasis energy V order σ n)) 0 τ :=
  rfl

private theorem support_dysonBasis_subset_reachableSupport (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ∀ order τ n, (dysonBasis energy V order τ n).support ⊆ reachableSupport V order n := by
  intro order
  induction order with
  | zero =>
      intro τ n
      simp [dysonBasis, basisState, reachableSupport]
  | succ order ih =>
      intro τ n
      rw [dysonBasis_succ]
      simpa using support_finiteSupportIntervalIntegral_subset
        (reachableSupport V (order + 1) n)
        (fun σ => interactionPicture energy V σ (dysonBasis energy V order σ n))
        0 τ

private theorem dysonBasis_succ_apply (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (m n : Config) :
    dysonBasis energy V (order + 1) τ n m =
      - ∫ σ in (0 : ℝ)..τ,
          interactionPicture energy V σ (dysonBasis energy V order σ n) m := by
  rw [dysonBasis_succ]
  change - finiteSupportIntervalIntegral (reachableSupport V (order + 1) n)
      (fun σ => interactionPicture energy V σ (dysonBasis energy V order σ n))
      0 τ m = _
  rw [finiteSupportIntervalIntegral_apply]
  intro σ
  exact support_interactionPicture_apply_subset_reachableSupport_succ energy V σ order n
    (dysonBasis energy V order σ n)
    (support_dysonBasis_subset_reachableSupport energy V order σ n)

/-- The canonical finite-order Dyson coefficient on an arbitrary configuration type. -/
noncomputable def dysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config (dysonBasis energy V order τ)

private theorem dysonCoeff_basisState (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (n : Config) :
    dysonCoeff energy V order τ (basisState n) = dysonBasis energy V order τ n := by
  change Finsupp.lift _ ℂ _ (dysonBasis energy V order τ) (Finsupp.single n 1) = _
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

@[simp]
theorem dysonCoeff_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    dysonCoeff energy V 0 τ = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro n c
  simp only [dysonCoeff, dysonBasis, Finsupp.lift_apply, LinearMap.id_apply]
  simpa [basisState] using (Finsupp.smul_single_one n c).symm

/-- Matrix-coordinate form of the recursive Dyson equation on a basis input. -/
theorem dysonCoeff_succ_basisState_apply (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (m n : Config) :
    dysonCoeff energy V (order + 1) τ (basisState n) m =
      - ∫ σ in (0 : ℝ)..τ,
          interactionPicture energy V σ
            (dysonCoeff energy V order σ (basisState n)) m := by
  rw [dysonCoeff_basisState]
  simpa only [dysonCoeff_basisState] using dysonBasis_succ_apply energy V order τ m n

/-- Every finite-order operator column is supported in the corresponding reachable set. -/
theorem support_dysonCoeff_basisState_subset_reachableSupport (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (n : Config) :
    (dysonCoeff energy V order τ (basisState n)).support ⊆ reachableSupport V order n := by
  rw [dysonCoeff_basisState]
  exact support_dysonBasis_subset_reachableSupport energy V order τ n

private theorem linearMap_apply_eq_finsetSum_of_support_subset
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
      change x k * matrixCoeff A m k = matrixCoeff A m k * x k
      exact mul_comm _ _

private theorem continuous_dysonCoeff_basisState_apply (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ∀ (order : ℕ) (m n : Config),
      Continuous (fun τ : ℝ => dysonCoeff energy V order τ (basisState n) m) := by
  intro order
  induction order with
  | zero =>
      intro m n
      simp only [dysonCoeff_zero, LinearMap.id_apply]
      exact continuous_const
  | succ order ih =>
      intro m n
      simp only [dysonCoeff_succ_basisState_apply]
      have hcont : Continuous (fun σ : ℝ =>
          interactionPicture energy V σ
            (dysonCoeff energy V order σ (basisState n)) m) := by
        let S := reachableSupport V order n
        have heq : (fun σ : ℝ => interactionPicture energy V σ
              (dysonCoeff energy V order σ (basisState n)) m) =
            (fun σ : ℝ => ∑ k ∈ S,
              matrixCoeff (interactionPicture energy V σ) m k *
                dysonCoeff energy V order σ (basisState n) k) := by
          funext σ
          exact linearMap_apply_eq_finsetSum_of_support_subset
            (interactionPicture energy V σ)
            (dysonCoeff energy V order σ (basisState n)) S
            (support_dysonCoeff_basisState_subset_reachableSupport energy V order σ n) m
        rw [heq]
        exact continuous_finsetSum S fun k _ =>
          (continuous_matrixCoeff_interactionPicture energy V m k).mul (ih k n)
      exact (intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0).neg

/-- Every matrix coefficient of a finite-order Dyson coefficient is continuous in imaginary time,
without requiring a finite ambient configuration type. -/
theorem continuous_matrixCoeff_dysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (m n : Config) :
    Continuous (fun τ : ℝ => matrixCoeff (dysonCoeff energy V order τ) m n) := by
  change Continuous (fun τ : ℝ => dysonCoeff energy V order τ (basisState n) m)
  exact continuous_dysonCoeff_basisState_apply energy V order m n

/-- Every matrix coefficient of a finite-order Dyson coefficient is interval-integrable. -/
theorem intervalIntegrable_matrixCoeff_dysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ)
    (m n : Config) (a b : ℝ) :
    IntervalIntegrable (fun τ : ℝ => matrixCoeff (dysonCoeff energy V order τ) m n)
      MeasureTheory.volume a b :=
  (continuous_matrixCoeff_dysonCoeff energy V order m n).intervalIntegrable a b

/-- At zero imaginary time, only the zeroth Dyson coefficient is nonzero. -/
theorem dysonCoeff_at_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) :
    dysonCoeff energy V n 0 = if n = 0 then LinearMap.id else 0 := by
  cases n with
  | zero => simp [dysonCoeff_zero]
  | succ k =>
      simp only [Nat.succ_ne_zero, if_false]
      apply matrixCoeff_ext
      intro m n'
      change dysonCoeff energy V (k + 1) 0 (basisState n') m = matrixCoeff 0 m n'
      rw [dysonCoeff_succ_basisState_apply, intervalIntegral.integral_same]
      simp [matrixCoeff]

variable [Fintype Config]

/-- On a finite configuration type, the canonical reachable-support coefficient satisfies the
operator-valued Dyson recursion reconstructed by `operatorIntervalIntegral`. -/
theorem dysonCoeff_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ) :
    dysonCoeff energy V (n + 1) τ =
      - operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ := by
  apply matrixCoeff_ext
  intro m n'
  change dysonCoeff energy V (n + 1) τ (basisState n') m =
    matrixCoeff
      (- operatorIntervalIntegral
        (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n'
  rw [dysonCoeff_succ_basisState_apply]
  have hneg : matrixCoeff
      (- operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' =
        - matrixCoeff (operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' := by
    simp [matrixCoeff]
  rw [hneg, matrixCoeff_operatorIntervalIntegral]
  congr 1

/-- The first-order coefficient is the negative interval integral of the interaction-picture
operator. -/
theorem dysonCoeff_one (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    dysonCoeff energy V 1 τ = - operatorIntervalIntegral (interactionPicture energy V) 0 τ := by
  rw [show 1 = 0 + 1 by omega, dysonCoeff_succ]
  congr 2
  funext σ
  rw [dysonCoeff_zero, LinearMap.comp_id]

/-- Matrix-coefficient form of the finite Dyson successor recursion. -/
theorem matrixCoeff_dysonCoeff_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : ℕ) (τ : ℝ)
    (m n' : Config) :
    matrixCoeff (dysonCoeff energy V (n + 1) τ) m n' =
      - ∫ σ in (0 : ℝ)..τ, ∑ k : Config,
          matrixCoeff (interactionPicture energy V σ) m k *
            matrixCoeff (dysonCoeff energy V n σ) k n' := by
  rw [dysonCoeff_succ]
  have hneg : matrixCoeff
      (- operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' =
        - matrixCoeff (operatorIntervalIntegral
          (fun σ => (interactionPicture energy V σ).comp (dysonCoeff energy V n σ)) 0 τ) m n' := by
    simp [matrixCoeff]
  rw [hneg, matrixCoeff_operatorIntervalIntegral]
  congr 1
  exact intervalIntegral.integral_congr fun σ _ => matrixCoeff_comp _ _ m n'

/-- The order-`N` finite Dyson truncation in the perturbation parameter `lam`. -/
noncomputable def dysonTruncation (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (lam : ℂ) (N : ℕ) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  ∑ n ∈ Finset.range (N + 1), lam ^ n • dysonCoeff energy V n τ

end Common
end SecondQuantization
