import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Creation
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
namespace AlgebraicFock

section Dual

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Algebraic annihilation by a linear functional, bundled as the canonical linear map from dual
vectors to left-contraction endomorphisms. -/
noncomputable def annihilateDual :
    Module.Dual ℂ 𝓗₁ →ₗ[ℂ] (AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ 𝓗₁))

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

/-- Exterior transport commutes with dual contraction when the dual functional is pulled back
along the one-particle linear map. No inner product or invertibility is required. -/
theorem annihilateDual_map
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (d : Module.Dual ℂ W) (Ψ : AlgebraicFock V) :
    annihilateDual W d (ExteriorAlgebra.map f Ψ) =
      ExteriorAlgebra.map f (annihilateDual V (d.comp f) Ψ) := by
  have hcreate (v : V) (x : AlgebraicFock V) :
      ExteriorAlgebra.map f (create V v x) =
        create W (f v) (ExteriorAlgebra.map f x) := by
    simp only [create_apply, oneParticle, map_mul, ExteriorAlgebra.map_apply_ι]
  induction Ψ using CliffordAlgebra.left_induction with
  | algebraMap c => simp [annihilateDual]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
      change annihilateDual W d (ExteriorAlgebra.map f (create V v x)) =
        ExteriorAlgebra.map f (annihilateDual V (d.comp f) (create V v x))
      rw [hcreate, annihilateDual_create_apply, annihilateDual_create_apply,
        map_sub, map_smul, hcreate, hx]
      rfl

end Dual

section InnerProduct

variable (𝓗₁ : Type*) [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁]

/-- The inner-product dual `f ↦ (g ↦ inner ℂ f g)`, bundled with its canonical conjugate-linearity
in the smearing vector. -/
noncomputable def innerDual : 𝓗₁ →ₗ⋆[ℂ] Module.Dual ℂ 𝓗₁ :=
  innerₛₗ ℂ

@[simp]
theorem innerDual_apply (f g : 𝓗₁) :
    innerDual 𝓗₁ f g = inner ℂ f g :=
  rfl

/-- The smeared annihilation field, bundled as the conjugate-linear map obtained by composing the
inner-product dual with left contraction. -/
noncomputable def annihilate :
    𝓗₁ →ₗ⋆[ℂ] (AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :=
  (annihilateDual 𝓗₁).comp (innerDual 𝓗₁)

/-- A one-particle linear isometry intertwines smeared annihilation fields through its exterior
lift. Surjectivity, finite-dimensionality, and completeness are not needed. -/
theorem annihilate_map
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (e : V →ₗᵢ[ℂ] W) (v : V) (Ψ : AlgebraicFock V) :
    annihilate W (e v) (ExteriorAlgebra.map e.toLinearMap Ψ) =
      ExteriorAlgebra.map e.toLinearMap (annihilate V v Ψ) := by
  have hdual : (innerDual W (e v)).comp e.toLinearMap = innerDual V v := by
    ext w
    exact e.inner_map_map v w
  have h := annihilateDual_map e.toLinearMap (innerDual W (e v)) Ψ
  rw [hdual] at h
  exact h

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

end AlgebraicFock
end Fermionic
end SecondQuantization
