import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationLinearity
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Lie-algebra functoriality of fermionic second quantization

Second quantization is a complex-linear Lie algebra homomorphism from one-particle endomorphisms to
finite-particle endomorphisms. In particular, it sends the commutator of one-particle operators to
the commutator of their second quantizations:

```text
[dGamma S, dGamma T] = dGamma [S, T].
```

Mathlib's `LieHom` and associative-endomorphism Lie bracket supply the canonical bundled structure.
-/

namespace SecondQuantization
namespace Fermionic
namespace AlgebraicFock

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

private theorem dGamma_lie_raw (S T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    ⁅dGamma 𝓗₁ S, dGamma 𝓗₁ T⁆ =
      dGamma 𝓗₁ (⁅S, T⁆) := by
  apply LinearMap.ext
  intro Ψ
  change
    dGamma 𝓗₁ S (dGamma 𝓗₁ T Ψ) - dGamma 𝓗₁ T (dGamma 𝓗₁ S Ψ) =
      dGamma 𝓗₁ (⁅S, T⁆) Ψ
  induction Ψ using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy =>
      simp only [map_add]
      calc
        dGamma 𝓗₁ S (dGamma 𝓗₁ T x) + dGamma 𝓗₁ S (dGamma 𝓗₁ T y) -
              (dGamma 𝓗₁ T (dGamma 𝓗₁ S x) + dGamma 𝓗₁ T (dGamma 𝓗₁ S y)) =
            (dGamma 𝓗₁ S (dGamma 𝓗₁ T x) - dGamma 𝓗₁ T (dGamma 𝓗₁ S x)) +
              (dGamma 𝓗₁ S (dGamma 𝓗₁ T y) - dGamma 𝓗₁ T (dGamma 𝓗₁ S y)) := by
          abel
        _ = dGamma 𝓗₁ (⁅S, T⁆) x +
              dGamma 𝓗₁ (⁅S, T⁆) y := by
          rw [hx, hy]
  | ι_mul x f hx =>
      change
        dGamma 𝓗₁ S (dGamma 𝓗₁ T (oneParticle 𝓗₁ f * x)) -
            dGamma 𝓗₁ T (dGamma 𝓗₁ S (oneParticle 𝓗₁ f * x)) =
          dGamma 𝓗₁ (⁅S, T⁆) (oneParticle 𝓗₁ f * x)
      calc
        dGamma 𝓗₁ S (dGamma 𝓗₁ T (oneParticle 𝓗₁ f * x)) -
              dGamma 𝓗₁ T (dGamma 𝓗₁ S (oneParticle 𝓗₁ f * x)) =
            (oneParticle 𝓗₁ (S (T f)) * x +
                oneParticle 𝓗₁ (T f) * dGamma 𝓗₁ S x +
              (oneParticle 𝓗₁ (S f) * dGamma 𝓗₁ T x +
                oneParticle 𝓗₁ f * dGamma 𝓗₁ S (dGamma 𝓗₁ T x))) -
            (oneParticle 𝓗₁ (T (S f)) * x +
                oneParticle 𝓗₁ (S f) * dGamma 𝓗₁ T x +
              (oneParticle 𝓗₁ (T f) * dGamma 𝓗₁ S x +
                oneParticle 𝓗₁ f * dGamma 𝓗₁ T (dGamma 𝓗₁ S x))) := by
          rw [dGamma_oneParticle_mul, dGamma_oneParticle_mul]
          rw [map_add, map_add]
          rw [dGamma_oneParticle_mul, dGamma_oneParticle_mul,
            dGamma_oneParticle_mul, dGamma_oneParticle_mul]
        _ = oneParticle 𝓗₁ (S (T f) - T (S f)) * x +
              oneParticle 𝓗₁ f *
                (dGamma 𝓗₁ S (dGamma 𝓗₁ T x) -
                  dGamma 𝓗₁ T (dGamma 𝓗₁ S x)) := by
          rw [map_sub, sub_mul, mul_sub]
          abel
        _ = oneParticle 𝓗₁ (S (T f) - T (S f)) * x +
              oneParticle 𝓗₁ f * dGamma 𝓗₁ (⁅S, T⁆) x := by
          rw [hx]
        _ = dGamma 𝓗₁ (⁅S, T⁆) (oneParticle 𝓗₁ f * x) := by
          rw [dGamma_oneParticle_mul, LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Fermionic second quantization as a Lie algebra homomorphism between endomorphism algebras. -/
noncomputable def dGammaLieHom :
    (𝓗₁ →ₗ[ℂ] 𝓗₁) →ₗ⁅ℂ⁆
      (AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) where
  toLinearMap := dGammaLinear 𝓗₁
  map_lie' := by
    intro S T
    simpa [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp] using
      (dGamma_lie_raw 𝓗₁ S T).symm

@[simp]
theorem dGammaLieHom_apply (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    dGammaLieHom 𝓗₁ T = dGamma 𝓗₁ T :=
  rfl

/-- Second quantization preserves ordinary commutators. -/
theorem dGamma_lie (S T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    ⁅dGamma 𝓗₁ S, dGamma 𝓗₁ T⁆ =
      dGamma 𝓗₁ (⁅S, T⁆) := by
  simpa [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp] using
    (LieHom.map_lie (dGammaLieHom 𝓗₁) S T).symm

/-- The algebraic total particle-number operator, identified as `dGamma id`.

On the completed full Fock space this operator is generally unbounded; here it is only an
algebraic endomorphism of the finite-particle exterior algebra. -/
noncomputable def totalNumberOperator :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  dGamma 𝓗₁ LinearMap.id

@[simp]
theorem totalNumberOperator_vacuum :
    totalNumberOperator 𝓗₁ (vacuum 𝓗₁) = 0 := by
  simp [totalNumberOperator]

@[simp]
theorem totalNumberOperator_oneParticle (f : 𝓗₁) :
    totalNumberOperator 𝓗₁ (oneParticle 𝓗₁ f) = oneParticle 𝓗₁ f := by
  simp [totalNumberOperator]

/-- Adding one exterior generator raises the algebraic number operator by one. -/
theorem totalNumberOperator_oneParticle_mul (f : 𝓗₁) (Ψ : AlgebraicFock 𝓗₁) :
    totalNumberOperator 𝓗₁ (oneParticle 𝓗₁ f * Ψ) =
      oneParticle 𝓗₁ f * Ψ + oneParticle 𝓗₁ f * totalNumberOperator 𝓗₁ Ψ := by
  simpa [totalNumberOperator] using dGamma_oneParticle_mul 𝓗₁ LinearMap.id f Ψ

/-- Every second-quantized one-particle operator commutes with total particle number. -/
theorem totalNumberOperator_commutes_dGamma (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    ⁅totalNumberOperator 𝓗₁, dGamma 𝓗₁ T⁆ = 0 := by
  rw [totalNumberOperator, dGamma_lie]
  have h : ⁅(LinearMap.id : 𝓗₁ →ₗ[ℂ] 𝓗₁), T⁆ = 0 := by
    apply LinearMap.ext
    intro f
    simp [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp]
  rw [h, dGamma_zero]

end AlgebraicFock
end Fermionic
end SecondQuantization
