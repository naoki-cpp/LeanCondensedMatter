import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Basic
import Mathlib.Algebra.Algebra.Bilinear

set_option linter.style.header false

/-!
# Basis-independent fermionic creation fields

Creation by a one-particle vector `f` is left exterior multiplication by its canonical degree-one
image:

```text
a†(f) Ψ = f ∧ Ψ.
```

The construction uses only the complex vector-space structure of the one-particle space. The
exterior-algebra relations give the creation-creation canonical anticommutation relations directly.
-/

namespace SecondQuantization
namespace Fermionic
namespace AlgebraicFock

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- The smeared fermionic creation field, bundled as the canonical complex-linear map from
one-particle vectors to left-multiplication endomorphisms of algebraic Fock space. -/
noncomputable def create :
    𝓗₁ →ₗ[ℂ] (AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :=
  (Algebra.lmul ℂ (AlgebraicFock 𝓗₁)).toLinearMap.comp (oneParticle 𝓗₁)

@[simp]
theorem create_apply (f : 𝓗₁) (Ψ : AlgebraicFock 𝓗₁) :
    create 𝓗₁ f Ψ = oneParticle 𝓗₁ f * Ψ :=
  rfl

/-- Degree-one one-particle vectors anticommute inside the exterior algebra. -/
theorem oneParticle_mul_add_swap (f g : 𝓗₁) :
    oneParticle 𝓗₁ f * oneParticle 𝓗₁ g +
      oneParticle 𝓗₁ g * oneParticle 𝓗₁ f = 0 := by
  simpa only [oneParticle] using
    (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) f g)

/-- Two smeared creation operators satisfy the creation-creation CAR. -/
theorem create_comp_add_swap (f g : 𝓗₁) :
    (create 𝓗₁ f).comp (create 𝓗₁ g) +
      (create 𝓗₁ g).comp (create 𝓗₁ f) = 0 := by
  have h := congrArg (Algebra.lmul ℂ (AlgebraicFock 𝓗₁))
    (oneParticle_mul_add_swap 𝓗₁ f g)
  change
    (Algebra.lmul ℂ (AlgebraicFock 𝓗₁) (oneParticle 𝓗₁ f)).comp
        (Algebra.lmul ℂ (AlgebraicFock 𝓗₁) (oneParticle 𝓗₁ g)) +
      (Algebra.lmul ℂ (AlgebraicFock 𝓗₁) (oneParticle 𝓗₁ g)).comp
        (Algebra.lmul ℂ (AlgebraicFock 𝓗₁) (oneParticle 𝓗₁ f)) = 0
  simpa only [map_add, map_mul, map_zero, Module.End.mul_eq_comp] using h

/-- Creating twice in the same one-particle state gives zero. -/
@[simp]
theorem create_comp_self (f : 𝓗₁) :
    (create 𝓗₁ f).comp (create 𝓗₁ f) = 0 := by
  have h := create_comp_add_swap 𝓗₁ f f
  have htwo : (2 : ℂ) • ((create 𝓗₁ f).comp (create 𝓗₁ f)) = 0 := by
    simpa [two_smul] using h
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end AlgebraicFock
end Fermionic
end SecondQuantization
