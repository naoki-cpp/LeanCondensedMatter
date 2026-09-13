import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantization

set_option linter.style.header false

/-!
# Linearity of fermionic second quantization

The recursive characterization of `dGamma` determines it uniquely on the exterior algebra and makes
the assignment

```text
T ↦ dGamma T
```

complex-linear. The proofs use basis-independent induction on the exterior algebra generators.
-/

namespace SecondQuantization
namespace Fermionic
namespace AlgebraicFock

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Second quantization vanishes on every scalar (zero-particle) state. -/
@[simp]
theorem dGamma_algebraMap (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) (c : ℂ) :
    dGamma 𝓗₁ T (algebraMap ℂ (AlgebraicFock 𝓗₁) c) = 0 := by
  simpa [dGamma] using
    (CliffordAlgebra.foldr'_algebraMap
      (Q := (0 : QuadraticForm ℂ 𝓗₁))
      (secondQuantizationStep 𝓗₁ T) (secondQuantizationStep_fold_condition 𝓗₁ T)
      (0 : AlgebraicFock 𝓗₁) c)

/-- The zero one-particle operator second-quantizes to the zero Fock-space operator. -/
@[simp]
theorem dGamma_zero :
    dGamma 𝓗₁ (0 : 𝓗₁ →ₗ[ℂ] 𝓗₁) = 0 := by
  apply LinearMap.ext
  intro Ψ
  change dGamma 𝓗₁ (0 : 𝓗₁ →ₗ[ℂ] 𝓗₁) Ψ = 0
  induction Ψ using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | ι_mul x f hx =>
      simpa [oneParticle, hx] using
        (dGamma_oneParticle_mul 𝓗₁ (0 : 𝓗₁ →ₗ[ℂ] 𝓗₁) f x)

/-- Second quantization is additive in the one-particle operator. -/
theorem dGamma_add (S T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    dGamma 𝓗₁ (S + T) = dGamma 𝓗₁ S + dGamma 𝓗₁ T := by
  apply LinearMap.ext
  intro Ψ
  change dGamma 𝓗₁ (S + T) Ψ = dGamma 𝓗₁ S Ψ + dGamma 𝓗₁ T Ψ
  induction Ψ using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]
      abel
  | ι_mul x f hx =>
      change dGamma 𝓗₁ (S + T) (oneParticle 𝓗₁ f * x) =
        dGamma 𝓗₁ S (oneParticle 𝓗₁ f * x) +
          dGamma 𝓗₁ T (oneParticle 𝓗₁ f * x)
      rw [dGamma_oneParticle_mul, dGamma_oneParticle_mul, dGamma_oneParticle_mul]
      simp only [LinearMap.add_apply, map_add, add_mul, mul_add, hx]
      abel

/-- Second quantization commutes with complex scalar multiplication. -/
theorem dGamma_smul (c : ℂ) (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    dGamma 𝓗₁ (c • T) = c • dGamma 𝓗₁ T := by
  apply LinearMap.ext
  intro Ψ
  change dGamma 𝓗₁ (c • T) Ψ = c • dGamma 𝓗₁ T Ψ
  induction Ψ using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp [map_add, hx, hy, smul_add]
  | ι_mul x f hx =>
      change dGamma 𝓗₁ (c • T) (oneParticle 𝓗₁ f * x) =
        c • dGamma 𝓗₁ T (oneParticle 𝓗₁ f * x)
      rw [dGamma_oneParticle_mul, dGamma_oneParticle_mul]
      simp [hx, smul_add]

/-- The basis-independent second-quantization construction as a linear map between endomorphism
spaces. -/
noncomputable def dGammaLinear :
    (𝓗₁ →ₗ[ℂ] 𝓗₁) →ₗ[ℂ]
      (AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) where
  toFun := dGamma 𝓗₁
  map_add' := dGamma_add 𝓗₁
  map_smul' := dGamma_smul 𝓗₁

@[simp]
theorem dGammaLinear_apply (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    dGammaLinear 𝓗₁ T = dGamma 𝓗₁ T :=
  rfl

end AlgebraicFock
end Fermionic
end SecondQuantization
