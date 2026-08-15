import LeanCondensedMatter.Analysis.Operator.LinearCommutator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationLinearity

set_option linter.style.header false

/-!
# Commutator functoriality of fermionic second quantization

This module completes the algebraic functorial core of F3 in issue #524. Second quantization sends
the commutator of one-particle endomorphisms to the commutator of their induced finite-particle
endomorphisms:

```text
[dGamma S, dGamma T] = dGamma [S, T].
```

The ordinary linear-map commutator itself is owned upstream by
`Analysis.Operator.LinearCommutator`; this module retains the historical `AlgebraicFock` name as a
compatibility abbreviation and proves the second-quantization functoriality theorem.
-/

namespace SecondQuantization
namespace Fermionic
namespace AlgebraicFock

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Compatibility abbreviation for the representation-independent linear commutator. -/
noncomputable abbrev linearCommutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  ConservationLaw.linearCommutator S T

@[simp]
theorem linearCommutator_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S T : V →ₗ[ℂ] V) (v : V) :
    linearCommutator S T v = S (T v) - T (S v) :=
  rfl

/-- Second quantization preserves ordinary commutators. -/
theorem dGamma_linearCommutator (S T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    linearCommutator (dGamma 𝓗₁ S) (dGamma 𝓗₁ T) =
      dGamma 𝓗₁ (linearCommutator S T) := by
  apply LinearMap.ext
  intro Ψ
  change
    dGamma 𝓗₁ S (dGamma 𝓗₁ T Ψ) - dGamma 𝓗₁ T (dGamma 𝓗₁ S Ψ) =
      dGamma 𝓗₁ (linearCommutator S T) Ψ
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
        _ = dGamma 𝓗₁ (linearCommutator S T) x +
              dGamma 𝓗₁ (linearCommutator S T) y := by
          rw [hx, hy]
  | ι_mul x f hx =>
      change
        dGamma 𝓗₁ S (dGamma 𝓗₁ T (oneParticle 𝓗₁ f * x)) -
            dGamma 𝓗₁ T (dGamma 𝓗₁ S (oneParticle 𝓗₁ f * x)) =
          dGamma 𝓗₁ (linearCommutator S T) (oneParticle 𝓗₁ f * x)
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
              oneParticle 𝓗₁ f * dGamma 𝓗₁ (linearCommutator S T) x := by
          rw [hx]
        _ = dGamma 𝓗₁ (linearCommutator S T) (oneParticle 𝓗₁ f * x) := by
          rw [dGamma_oneParticle_mul, linearCommutator_apply]

/-- The algebraic total particle-number operator, identified as `dGamma id`.

On the completed full Fock space this operator is generally unbounded; here it is only an
algebraic endomorphism of the finite-particle exterior algebra. -/
noncomputable def numberOperator :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  dGamma 𝓗₁ LinearMap.id

@[simp]
theorem numberOperator_vacuum :
    numberOperator 𝓗₁ (vacuum 𝓗₁) = 0 := by
  simp [numberOperator]

@[simp]
theorem numberOperator_oneParticle (f : 𝓗₁) :
    numberOperator 𝓗₁ (oneParticle 𝓗₁ f) = oneParticle 𝓗₁ f := by
  simp [numberOperator]

/-- Adding one exterior generator raises the algebraic number operator by one. -/
theorem numberOperator_oneParticle_mul (f : 𝓗₁) (Ψ : AlgebraicFock 𝓗₁) :
    numberOperator 𝓗₁ (oneParticle 𝓗₁ f * Ψ) =
      oneParticle 𝓗₁ f * Ψ + oneParticle 𝓗₁ f * numberOperator 𝓗₁ Ψ := by
  simpa [numberOperator] using dGamma_oneParticle_mul 𝓗₁ LinearMap.id f Ψ

/-- Every second-quantized one-particle operator commutes with total particle number. -/
theorem numberOperator_commutes_dGamma (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    linearCommutator (numberOperator 𝓗₁) (dGamma 𝓗₁ T) = 0 := by
  rw [numberOperator, dGamma_linearCommutator]
  have h : linearCommutator (LinearMap.id : 𝓗₁ →ₗ[ℂ] 𝓗₁) T = 0 := by
    apply LinearMap.ext
    intro f
    simp [linearCommutator, ConservationLaw.linearCommutator]
  rw [h, dGamma_zero]

end AlgebraicFock
end Fermionic
end SecondQuantization
