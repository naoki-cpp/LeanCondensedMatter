import LeanCondensedMatter.SecondQuantization.Fermionic.Field.BoundedKuboBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.RankOneSecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FiniteHilbertCreationAnnihilation

set_option linter.style.header false

/-!
# Adjoint reversal for second-quantized lattice matrix units

The basis-independent identity

```text
dGamma (|x><y|) = a†(x) a(y)
```

is transported through the canonical occupation equivalence and then to the finite-dimensional
Hilbert Fock space. Since bounded occupation creation and annihilation are mutual adjoints, the
resulting matrix-unit operator has the expected adjoint:

```text
(dGamma (|x><y|))† = dGamma (|y><x|).
```

This module supplies the structural input for deriving self-adjoint hopping Hamiltonians and bond
currents from coefficient-level Hermiticity.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]
variable {𝓗₁ : Type*} [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Conjugation by the occupation/exterior equivalence preserves composition. -/
theorem occupationConjugate_comp
    (b : Module.Basis Mode ℂ 𝓗₁)
    (A B : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :
    occupationConjugate b (A.comp B) =
      (occupationConjugate b A).comp (occupationConjugate b B) := by
  apply LinearMap.ext
  intro Ψ
  apply (occupationEquiv b).injective
  calc
    occupationEquiv b (occupationConjugate b (A.comp B) Ψ) =
        (A.comp B) (occupationEquiv b Ψ) :=
      occupationEquiv_occupationConjugate_apply b (A.comp B) Ψ
    _ = A (B (occupationEquiv b Ψ)) := rfl
    _ = A (occupationEquiv b (occupationConjugate b B Ψ)) := by
      rw [occupationEquiv_occupationConjugate_apply]
    _ = occupationEquiv b
        (occupationConjugate b A (occupationConjugate b B Ψ)) :=
      (occupationEquiv_occupationConjugate_apply b A
        (occupationConjugate b B Ψ)).symm

/-- Exterior creation by a basis vector conjugates to occupation creation in the corresponding
mode. -/
theorem occupationConjugate_create
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    occupationConjugate b (create 𝓗₁ (b i)) =
      SecondQuantization.Fermionic.create i := by
  apply LinearMap.ext
  intro Ψ
  apply (occupationEquiv b).injective
  rw [occupationEquiv_occupationConjugate_apply]
  have h := LinearMap.congr_fun (occupationEquiv_create b i) Ψ
  simpa [LinearMap.comp_apply] using h.symm

variable {Site : Type*}

@[simp]
theorem latticeBasis_apply_eq_latticeKet (x : Site) :
    latticeBasis (Site := Site) x = latticeKet x := by
  rfl

@[simp]
theorem latticeBasis_coord_eq_latticeCoordinateDual (y : Site) :
    (latticeBasis (Site := Site)).coord y = latticeCoordinateDual y := by
  apply LinearMap.ext
  intro ψ
  simp [latticeBasis, latticeCoordinateDual]

variable [LinearOrder Site]

/-- In occupation representation, a second-quantized lattice matrix unit is the standard
creation-annihilation bilinear. -/
theorem occupationOperator_dGamma_matrixUnit (x y : Site) :
    occupationOperator
        (dGamma (LatticeState Site) (matrixUnit x y)) =
      (SecondQuantization.Fermionic.create x).comp
        (SecondQuantization.Fermionic.annihilate y) := by
  change occupationConjugate (latticeBasis (Site := Site))
      (dGamma (LatticeState Site) (matrixUnit x y)) = _
  rw [dGamma_matrixUnit, occupationConjugate_comp]
  rw [← latticeBasis_apply_eq_latticeKet (Site := Site) x,
    ← latticeBasis_coord_eq_latticeCoordinateDual (Site := Site) y]
  rw [occupationConjugate_create]
  change
    (SecondQuantization.Fermionic.create x).comp
        (occupationAnnihilateFromField (latticeBasis (Site := Site)) y) = _
  rw [occupationAnnihilateFromField_eq_annihilate]

section Finite

variable [Fintype Site]

/-- Bounded finite-Hilbert realization of a second-quantized one-particle matrix unit. -/
noncomputable def boundedDgammaMatrixUnit (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (dGamma (LatticeState Site) (matrixUnit x y))

/-- The bounded matrix-unit realization is the finite-Hilbert creation-annihilation bilinear. -/
theorem boundedDgammaMatrixUnit_eq_create_comp_annihilate (x y : Site) :
    boundedDgammaMatrixUnit x y =
      (finiteHilbertCreate x).comp (finiteHilbertAnnihilate y) := by
  change Common.finiteHilbertOperator
      (occupationOperator (dGamma (LatticeState Site) (matrixUnit x y))) = _
  rw [occupationOperator_dGamma_matrixUnit, Common.finiteHilbertOperator_comp]
  rfl

/-- Taking the Hilbert-space adjoint reverses the oriented one-particle matrix unit. -/
@[simp]
theorem star_boundedDgammaMatrixUnit (x y : Site) :
    star (boundedDgammaMatrixUnit x y) = boundedDgammaMatrixUnit y x := by
  rw [boundedDgammaMatrixUnit_eq_create_comp_annihilate,
    boundedDgammaMatrixUnit_eq_create_comp_annihilate]
  change
    star (finiteHilbertCreate x * finiteHilbertAnnihilate y) =
      finiteHilbertCreate y * finiteHilbertAnnihilate x
  rw [star_mul, star_finiteHilbertAnnihilate, star_finiteHilbertCreate]

end Finite

end
end Field
end Fermionic
end SecondQuantization
