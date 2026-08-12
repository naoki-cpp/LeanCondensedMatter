import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Creation
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold

set_option linter.style.header false

/-!
# Basis-independent fermionic second quantization

This module begins F3 of issue #524. A one-particle linear operator `T : 𝓗₁ →ₗ[ℂ] 𝓗₁`
induces the degree-preserving operator `dΓ(T)` on the algebraic finite-particle Fock space. It is
characterized recursively by

```text
dΓ(T) 1 = 0,
dΓ(T) (f ∧ Ψ) = Tf ∧ Ψ + f ∧ dΓ(T) Ψ.
```

The construction uses `CliffordAlgebra.foldr'` at the zero quadratic form, so it is independent of
a basis and requires no finite-dimensionality, inner product, completion, or boundedness assumption.
-/

namespace SecondQuantization
namespace Fermionic
namespace AlgebraicFock

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The bilinear recursion step used to extend a one-particle operator to the exterior algebra. -/
noncomputable def secondQuantizationStep (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    𝓗₁ →ₗ[ℂ]
      (AlgebraicFock 𝓗₁ × AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) where
  toFun f :=
    { toFun := fun xdx =>
        oneParticle 𝓗₁ (T f) * xdx.1 + oneParticle 𝓗₁ f * xdx.2
      map_add' := by
        intro x y
        change
          oneParticle 𝓗₁ (T f) * (x.1 + y.1) +
              oneParticle 𝓗₁ f * (x.2 + y.2) =
            (oneParticle 𝓗₁ (T f) * x.1 + oneParticle 𝓗₁ f * x.2) +
              (oneParticle 𝓗₁ (T f) * y.1 + oneParticle 𝓗₁ f * y.2)
        simp only [mul_add]
        abel
      map_smul' := by
        intro c x
        change
          oneParticle 𝓗₁ (T f) * (c • x.1) + oneParticle 𝓗₁ f * (c • x.2) =
            c • (oneParticle 𝓗₁ (T f) * x.1 + oneParticle 𝓗₁ f * x.2)
        simp [smul_add] }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro xdx
    change
      oneParticle 𝓗₁ (T (f + g)) * xdx.1 + oneParticle 𝓗₁ (f + g) * xdx.2 =
        (oneParticle 𝓗₁ (T f) * xdx.1 + oneParticle 𝓗₁ f * xdx.2) +
          (oneParticle 𝓗₁ (T g) * xdx.1 + oneParticle 𝓗₁ g * xdx.2)
    simp only [map_add, add_mul]
    abel
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro xdx
    change
      oneParticle 𝓗₁ (T (c • f)) * xdx.1 + oneParticle 𝓗₁ (c • f) * xdx.2 =
        c • (oneParticle 𝓗₁ (T f) * xdx.1 + oneParticle 𝓗₁ f * xdx.2)
    simp [smul_add]

@[simp]
theorem secondQuantizationStep_apply (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : 𝓗₁)
    (x dx : AlgebraicFock 𝓗₁) :
    secondQuantizationStep 𝓗₁ T f (x, dx) =
      oneParticle 𝓗₁ (T f) * x + oneParticle 𝓗₁ f * dx :=
  rfl

/-- The recursion step respects the exterior relation `f ∧ f = 0`. -/
theorem secondQuantizationStep_square (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : 𝓗₁)
    (x dx : AlgebraicFock 𝓗₁) :
    secondQuantizationStep 𝓗₁ T f
        (oneParticle 𝓗₁ f * x, secondQuantizationStep 𝓗₁ T f (x, dx)) = 0 := by
  simp only [secondQuantizationStep_apply, mul_add, ← mul_assoc]
  rw [← add_assoc, ← add_mul, oneParticle_mul_add_swap, zero_mul]
  simp [oneParticle]

/-- The exact compatibility condition required by `CliffordAlgebra.foldr'` at the zero quadratic
form. -/
theorem secondQuantizationStep_fold_condition (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : 𝓗₁)
    (x dx : AlgebraicFock 𝓗₁) :
    secondQuantizationStep 𝓗₁ T f
        (CliffordAlgebra.ι (0 : QuadraticForm ℂ 𝓗₁) f * x,
          secondQuantizationStep 𝓗₁ T f (x, dx)) =
      (0 : QuadraticForm ℂ 𝓗₁) f • dx := by
  simpa [oneParticle] using secondQuantizationStep_square 𝓗₁ T f x dx

/-- The algebraic second quantization `dΓ(T)` of a one-particle linear operator `T`.

It acts on each finite wedge by applying `T` in every slot and summing the results. -/
noncomputable def dGamma (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  CliffordAlgebra.foldr' (0 : QuadraticForm ℂ 𝓗₁)
    (secondQuantizationStep 𝓗₁ T) (secondQuantizationStep_fold_condition 𝓗₁ T)
    (0 : AlgebraicFock 𝓗₁)

/-- Second quantization kills the vacuum. -/
@[simp]
theorem dGamma_vacuum (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) :
    dGamma 𝓗₁ T (vacuum 𝓗₁) = 0 := by
  simpa [dGamma, vacuum] using
    (CliffordAlgebra.foldr'_algebraMap
      (Q := (0 : QuadraticForm ℂ 𝓗₁))
      (secondQuantizationStep 𝓗₁ T) (secondQuantizationStep_fold_condition 𝓗₁ T)
      (0 : AlgebraicFock 𝓗₁) (1 : ℂ))

/-- On a one-particle state, `dΓ(T)` agrees with `T`. -/
@[simp]
theorem dGamma_oneParticle (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : 𝓗₁) :
    dGamma 𝓗₁ T (oneParticle 𝓗₁ f) = oneParticle 𝓗₁ (T f) := by
  simpa [dGamma, oneParticle, secondQuantizationStep] using
    (CliffordAlgebra.foldr'_ι
      (Q := (0 : QuadraticForm ℂ 𝓗₁))
      (secondQuantizationStep 𝓗₁ T) (secondQuantizationStep_fold_condition 𝓗₁ T)
      (0 : AlgebraicFock 𝓗₁) f)

/-- The defining Leibniz rule of `dΓ(T)` on a left one-particle wedge. -/
theorem dGamma_oneParticle_mul (T : 𝓗₁ →ₗ[ℂ] 𝓗₁) (f : 𝓗₁)
    (Ψ : AlgebraicFock 𝓗₁) :
    dGamma 𝓗₁ T (oneParticle 𝓗₁ f * Ψ) =
      oneParticle 𝓗₁ (T f) * Ψ + oneParticle 𝓗₁ f * dGamma 𝓗₁ T Ψ := by
  simpa [dGamma, oneParticle, secondQuantizationStep] using
    (CliffordAlgebra.foldr'_ι_mul
      (Q := (0 : QuadraticForm ℂ 𝓗₁))
      (secondQuantizationStep 𝓗₁ T) (secondQuantizationStep_fold_condition 𝓗₁ T)
      (0 : AlgebraicFock 𝓗₁) f Ψ)

end AlgebraicFock
end Fermionic
end SecondQuantization
