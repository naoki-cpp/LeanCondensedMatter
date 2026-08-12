import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationLinearity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.DiscreteLattice

set_option linter.style.header false

/-!
# Second quantization of algebraic rank-one maps

For a one-particle vector `f` and an algebraic dual vector `d`, the rank-one map

```text
g ↦ d(g) f
```

second-quantizes to the number-conserving field bilinear `a†(f) a(d)`. This statement is
basis-independent and requires neither finite dimensionality nor an inner product.

For lattice states, a matrix unit `|x><y|` is exactly the rank-one map formed from the site ket at
`x` and coordinate evaluation at `y`. The general theorem therefore gives an explicit field
factorization of `dGamma (matrixUnit x y)`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

variable (𝓗₁ : Type*) [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Algebraic rank-one endomorphism `g ↦ d(g) f`. -/
def dualRankOne (f : 𝓗₁) (d : Module.Dual ℂ 𝓗₁) : 𝓗₁ →ₗ[ℂ] 𝓗₁ where
  toFun g := d g • f
  map_add' g h := by simp [add_smul]
  map_smul' c g := by simp [smul_smul]

@[simp]
theorem dualRankOne_apply (f : 𝓗₁) (d : Module.Dual ℂ 𝓗₁) (g : 𝓗₁) :
    dualRankOne 𝓗₁ f d g = d g • f :=
  rfl

/-- The second quantization of an algebraic rank-one map is creation followed by contraction. -/
theorem dGamma_dualRankOne (f : 𝓗₁) (d : Module.Dual ℂ 𝓗₁) :
    dGamma 𝓗₁ (dualRankOne 𝓗₁ f d) =
      (create 𝓗₁ f).comp (annihilateDual 𝓗₁ d) := by
  apply LinearMap.ext
  intro Ψ
  induction Ψ using CliffordAlgebra.left_induction with
  | algebraMap c =>
      simp [dGamma_algebraMap, annihilateDual, create]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
  | ι_mul x g hx =>
      rw [dGamma_oneParticle_mul]
      change
        oneParticle 𝓗₁ (d g • f) * x +
            oneParticle 𝓗₁ g * dGamma 𝓗₁ (dualRankOne 𝓗₁ f d) x =
          create 𝓗₁ f
            (annihilateDual 𝓗₁ d (create 𝓗₁ g x))
      rw [annihilateDual_create_apply, hx]
      have hcar := congrArg
        (fun z => z * annihilateDual 𝓗₁ d x)
        (oneParticle_mul_add_swap 𝓗₁ f g)
      have hswap :
          oneParticle 𝓗₁ g *
              (oneParticle 𝓗₁ f * annihilateDual 𝓗₁ d x) =
            -(oneParticle 𝓗₁ f *
              (oneParticle 𝓗₁ g * annihilateDual 𝓗₁ d x)) := by
        rw [add_mul, zero_mul, mul_assoc, mul_assoc] at hcar
        exact eq_neg_of_add_eq_zero_right hcar
      simp only [create_apply, LinearMap.comp_apply, map_sub, map_smul]
      rw [smul_mul_assoc, hswap]
      abel

variable {Site : Type*}

/-- Coordinate evaluation at a lattice site as an algebraic dual vector. -/
def latticeCoordinateDual (y : Site) : Module.Dual ℂ (LatticeState Site) where
  toFun ψ := ψ y
  map_add' ψ φ := by simp
  map_smul' c ψ := by simp

@[simp]
theorem latticeCoordinateDual_apply (y : Site) (ψ : LatticeState Site) :
    latticeCoordinateDual y ψ = ψ y :=
  rfl

/-- A lattice matrix unit is the corresponding algebraic rank-one map. -/
theorem dualRankOne_latticeKet_latticeCoordinateDual (x y : Site) :
    dualRankOne (LatticeState Site) (latticeKet x) (latticeCoordinateDual y) =
      matrixUnit x y := by
  apply LinearMap.ext
  intro ψ
  simp [dualRankOne, latticeKet, latticeCoordinateDual, matrixUnit]

/-- The second quantization of a lattice matrix unit factors into creation and annihilation fields. -/
theorem dGamma_matrixUnit (x y : Site) :
    dGamma (LatticeState Site) (matrixUnit x y) =
      (create (LatticeState Site) (latticeKet x)).comp
        (annihilateDual (LatticeState Site) (latticeCoordinateDual y)) := by
  rw [← dualRankOne_latticeKet_latticeCoordinateDual]
  exact dGamma_dualRankOne (LatticeState Site) (latticeKet x) (latticeCoordinateDual y)

end
end Field
end Fermionic
end SecondQuantization
