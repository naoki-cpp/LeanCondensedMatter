import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

set_option linter.style.header false

/-!
# Basis-independent fermionic annihilation fields and CAR

A dual vector acts on exterior Fock space by left contraction. For a complex inner-product space, a
one-particle vector `f` supplies the dual functional `g ↦ inner ℂ f g`, so the physical annihilation
field is conjugate-linear in `f`.

The contraction identity

```text
a(f) (g ∧ Ψ) = inner ℂ f g • Ψ - g ∧ a(f) Ψ
```

gives the mixed canonical anticommutation relation directly.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

section Dual

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Algebraic annihilation by a linear functional, implemented as left contraction. -/
noncomputable def annihilateDual (d : Module.Dual ℂ 𝓗₁) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  CliffordAlgebra.contractLeft d

/-- Algebraic annihilation is linear in the dual vector. -/
theorem annihilateDual_add (d e : Module.Dual ℂ 𝓗₁) :
    annihilateDual 𝓗₁ (d + e) = annihilateDual 𝓗₁ d + annihilateDual 𝓗₁ e := by
  simpa only [annihilateDual] using
    (CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm ℂ 𝓗₁))).map_add d e

/-- Algebraic annihilation is homogeneous in the dual vector. -/
theorem annihilateDual_smul (c : ℂ) (d : Module.Dual ℂ 𝓗₁) :
    annihilateDual 𝓗₁ (c • d) = c • annihilateDual 𝓗₁ d := by
  simpa only [annihilateDual] using
    (CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm ℂ 𝓗₁))).map_smul c d

/-- A dual contraction kills the vacuum. -/
@[simp]
theorem annihilateDual_vacuum (d : Module.Dual ℂ 𝓗₁) :
    annihilateDual 𝓗₁ d (vacuum 𝓗₁) = 0 := by
  simpa [annihilateDual, vacuum] using
    (CliffordAlgebra.contractLeft_one (0 : QuadraticForm ℂ 𝓗₁) d)

/-- A dual contraction evaluates a one-particle state. -/
@[simp]
theorem annihilateDual_oneParticle (d : Module.Dual ℂ 𝓗₁) (f : 𝓗₁) :
    annihilateDual 𝓗₁ d (oneParticle 𝓗₁ f) =
      algebraMap ℂ (AlgebraicFock 𝓗₁) (d f) := by
  simpa [annihilateDual, oneParticle] using
    (CliffordAlgebra.contractLeft_ι (0 : QuadraticForm ℂ 𝓗₁) d f)

/-- Contraction through one created particle: the algebraic mixed-CAR identity. -/
theorem annihilateDual_create_apply (d : Module.Dual ℂ 𝓗₁) (g : 𝓗₁)
    (Ψ : AlgebraicFock 𝓗₁) :
    annihilateDual 𝓗₁ d (create 𝓗₁ g Ψ) =
      d g • Ψ - create 𝓗₁ g (annihilateDual 𝓗₁ d Ψ) := by
  simpa only [annihilateDual, create_apply, oneParticle] using
    (CliffordAlgebra.contractLeft_ι_mul
      (Q := (0 : QuadraticForm ℂ 𝓗₁)) d g Ψ)

/-- Two algebraic annihilation contractions anticommute. -/
theorem annihilateDual_comp_add_swap (d e : Module.Dual ℂ 𝓗₁) :
    (annihilateDual 𝓗₁ d).comp (annihilateDual 𝓗₁ e) +
      (annihilateDual 𝓗₁ e).comp (annihilateDual 𝓗₁ d) = 0 := by
  apply LinearMap.ext
  intro Ψ
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  change CliffordAlgebra.contractLeft d (CliffordAlgebra.contractLeft e Ψ) +
      CliffordAlgebra.contractLeft e (CliffordAlgebra.contractLeft d Ψ) = 0
  exact eq_neg_iff_add_eq_zero.mp (CliffordAlgebra.contractLeft_comm d e Ψ)

/-- Contracting twice by the same dual vector is zero. -/
@[simp]
theorem annihilateDual_comp_self (d : Module.Dual ℂ 𝓗₁) :
    (annihilateDual 𝓗₁ d).comp (annihilateDual 𝓗₁ d) = 0 := by
  apply LinearMap.ext
  intro Ψ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  exact CliffordAlgebra.contractLeft_contractLeft d Ψ

/-- Algebraic mixed CAR between contraction and exterior multiplication. -/
theorem annihilateDual_comp_create_add_swap (d : Module.Dual ℂ 𝓗₁) (g : 𝓗₁) :
    (annihilateDual 𝓗₁ d).comp (create 𝓗₁ g) +
      (create 𝓗₁ g).comp (annihilateDual 𝓗₁ d) =
        d g • (LinearMap.id : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) := by
  apply LinearMap.ext
  intro Ψ
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  rw [annihilateDual_create_apply]
  exact sub_add_cancel _ _

end Dual

section InnerProduct

variable (𝓗₁ : Type*) [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁]

/-- The linear functional `g ↦ inner ℂ f g` associated with `f`.

As a function of `f`, this dual vector is conjugate-linear. -/
noncomputable def innerDual (f : 𝓗₁) : Module.Dual ℂ 𝓗₁ :=
  ((innerSL ℂ) f).toLinearMap

@[simp]
theorem innerDual_apply (f g : 𝓗₁) :
    innerDual 𝓗₁ f g = inner ℂ f g := by
  simp [innerDual]

/-- The inner-product dual is additive in its vector argument. -/
theorem innerDual_add (f g : 𝓗₁) :
    innerDual 𝓗₁ (f + g) = innerDual 𝓗₁ f + innerDual 𝓗₁ g := by
  apply LinearMap.ext
  intro h
  simp [innerDual]

/-- The inner-product dual is conjugate-linear in its vector argument. -/
theorem innerDual_smul (c : ℂ) (f : 𝓗₁) :
    innerDual 𝓗₁ (c • f) = star c • innerDual 𝓗₁ f := by
  apply LinearMap.ext
  intro h
  simp [innerDual]

/-- The smeared annihilation operator `a(f)`, defined by contraction with `g ↦ inner ℂ f g`. -/
noncomputable def annihilate (f : 𝓗₁) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  annihilateDual 𝓗₁ (innerDual 𝓗₁ f)

/-- Smeared annihilation is additive in the smearing vector. -/
theorem annihilate_add (f g : 𝓗₁) :
    annihilate 𝓗₁ (f + g) = annihilate 𝓗₁ f + annihilate 𝓗₁ g := by
  change annihilateDual 𝓗₁ (innerDual 𝓗₁ (f + g)) =
    annihilateDual 𝓗₁ (innerDual 𝓗₁ f) + annihilateDual 𝓗₁ (innerDual 𝓗₁ g)
  rw [innerDual_add, annihilateDual_add]

/-- Smeared annihilation is conjugate-linear in the smearing vector. -/
theorem annihilate_smul (c : ℂ) (f : 𝓗₁) :
    annihilate 𝓗₁ (c • f) = star c • annihilate 𝓗₁ f := by
  change annihilateDual 𝓗₁ (innerDual 𝓗₁ (c • f)) =
    star c • annihilateDual 𝓗₁ (innerDual 𝓗₁ f)
  rw [innerDual_smul, annihilateDual_smul]

/-- A smeared annihilation field kills the vacuum. -/
@[simp]
theorem annihilate_vacuum (f : 𝓗₁) :
    annihilate 𝓗₁ f (vacuum 𝓗₁) = 0 := by
  simpa [annihilate] using annihilateDual_vacuum 𝓗₁ (innerDual 𝓗₁ f)

/-- Annihilation of a one-particle state returns its inner product with the smearing vector. -/
@[simp]
theorem annihilate_oneParticle (f g : 𝓗₁) :
    annihilate 𝓗₁ f (oneParticle 𝓗₁ g) =
      algebraMap ℂ (AlgebraicFock 𝓗₁) (inner ℂ f g) := by
  simpa [annihilate] using annihilateDual_oneParticle 𝓗₁ (innerDual 𝓗₁ f) g

/-- The annihilation-annihilation smeared CAR. -/
theorem annihilate_comp_add_swap (f g : 𝓗₁) :
    (annihilate 𝓗₁ f).comp (annihilate 𝓗₁ g) +
      (annihilate 𝓗₁ g).comp (annihilate 𝓗₁ f) = 0 := by
  simpa [annihilate] using
    annihilateDual_comp_add_swap 𝓗₁ (innerDual 𝓗₁ f) (innerDual 𝓗₁ g)

/-- Applying the same smeared annihilation operator twice gives zero. -/
@[simp]
theorem annihilate_comp_self (f : 𝓗₁) :
    (annihilate 𝓗₁ f).comp (annihilate 𝓗₁ f) = 0 := by
  simpa [annihilate] using annihilateDual_comp_self 𝓗₁ (innerDual 𝓗₁ f)

/-- The mixed smeared CAR `{a(f), a†(g)} = inner ℂ f g • I`. -/
theorem annihilate_comp_create_add_swap (f g : 𝓗₁) :
    (annihilate 𝓗₁ f).comp (create 𝓗₁ g) +
      (create 𝓗₁ g).comp (annihilate 𝓗₁ f) =
        inner ℂ f g •
          (LinearMap.id : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) := by
  simpa [annihilate] using
    annihilateDual_comp_create_add_swap 𝓗₁ (innerDual 𝓗₁ f) g

end InnerProduct

end Field
end Fermionic
end SecondQuantization
