import LeanCondensedMatter.SecondQuantization.Common.Perturbation.FiniteSupportIntegral

set_option linter.style.header false

/-!
# Finite-order Dyson coefficients on an infinite configuration space

For a fixed algebraic interaction, every basis state reaches only finitely many configurations at
any fixed Dyson order.  This file uses that finite reachable support to reconstruct each recursive
coefficient from scalar interval integrals without enumerating the ambient configuration type.

The construction is algebraic and finite-order.  It does not assert boundedness, completed-space
Bochner integrability, or convergence of the infinite Dyson series.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- The image of one basis state under a finite-order Dyson coefficient on an arbitrary
configuration type. -/
noncomputable def infiniteDysonBasis (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ℕ → ℝ → Config → AlgebraicFock Config
  | 0, _, n => basisState n
  | order + 1, τ, n =>
      - finiteSupportIntervalIntegral (reachableSupport V (order + 1) n)
          (fun σ => interactionPicture energy V σ (infiniteDysonBasis energy V order σ n)) 0 τ

@[simp]
theorem infiniteDysonBasis_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) (n : Config) :
    infiniteDysonBasis energy V 0 τ n = basisState n := rfl

@[simp]
theorem infiniteDysonBasis_succ (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (n : Config) :
    infiniteDysonBasis energy V (order + 1) τ n =
      - finiteSupportIntervalIntegral (reachableSupport V (order + 1) n)
          (fun σ => interactionPicture energy V σ (infiniteDysonBasis energy V order σ n)) 0 τ :=
  rfl

/-- Every finite-order basis image is supported in its finite reachable set. -/
theorem support_infiniteDysonBasis_subset_reachableSupport (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    ∀ order τ n,
      (infiniteDysonBasis energy V order τ n).support ⊆ reachableSupport V order n := by
  intro order
  induction order with
  | zero =>
      intro τ n
      simp [infiniteDysonBasis, basisState, reachableSupport]
  | succ order ih =>
      intro τ n
      rw [infiniteDysonBasis_succ]
      simpa using support_finiteSupportIntervalIntegral_subset
        (reachableSupport V (order + 1) n)
        (fun σ => interactionPicture energy V σ (infiniteDysonBasis energy V order σ n))
        0 τ

/-- The finite-order Dyson coefficient as a genuine algebraic-Fock linear operator on an arbitrary
configuration type. -/
noncomputable def infiniteDysonCoeff (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (order : ℕ) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config (infiniteDysonBasis energy V order τ)

@[simp]
theorem infiniteDysonCoeff_basisState (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (n : Config) :
    infiniteDysonCoeff energy V order τ (basisState n) =
      infiniteDysonBasis energy V order τ n := by
  change Finsupp.lift _ ℂ _ (infiniteDysonBasis energy V order τ) (Finsupp.single n 1) = _
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

@[simp]
theorem infiniteDysonCoeff_zero (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (τ : ℝ) :
    infiniteDysonCoeff energy V 0 τ = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro n c
  simp only [infiniteDysonCoeff, infiniteDysonBasis, Finsupp.lift_apply,
    Finsupp.sum_single_index, LinearMap.id_apply]
  simpa [basisState] using (Finsupp.smul_single_one n c).symm

/-- Basis-state form of the recursive Dyson equation. -/
theorem infiniteDysonCoeff_succ_basisState (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (n : Config) :
    infiniteDysonCoeff energy V (order + 1) τ (basisState n) =
      - finiteSupportIntervalIntegral (reachableSupport V (order + 1) n)
          (fun σ => interactionPicture energy V σ
            (infiniteDysonCoeff energy V order σ (basisState n))) 0 τ := by
  simp only [infiniteDysonCoeff_basisState, infiniteDysonBasis_succ]

/-- Every finite-order operator column is supported in the corresponding reachable set. -/
theorem support_infiniteDysonCoeff_basisState_subset_reachableSupport (energy : Config → ℝ)
    (V : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (order : ℕ) (τ : ℝ) (n : Config) :
    (infiniteDysonCoeff energy V order τ (basisState n)).support ⊆
      reachableSupport V order n := by
  rw [infiniteDysonCoeff_basisState]
  exact support_infiniteDysonBasis_subset_reachableSupport energy V order τ n

end Common
end SecondQuantization
