import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FiniteHilbertCreationAnnihilation

set_option linter.style.header false

/-!
# Adjoint reversal for second-quantized lattice matrix units

The basis-independent identity

```text
AlgebraicFock.dGamma (|x><y|) = a†(x) a(y)
```

is transported through the canonical occupation equivalence and then to the finite-dimensional
Hilbert Fock space. Since bounded occupation creation and annihilation are mutual adjoints, the
resulting matrix-unit operator has the expected adjoint:

```text
(AlgebraicFock.dGamma (|x><y|))† = AlgebraicFock.dGamma (|y><x|).
```

This module supplies the structural input for deriving self-adjoint hopping Hamiltonians and bond
currents from coefficient-level Hermiticity.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]
variable {𝓗₁ : Type*} [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Conjugation by the occupation/exterior equivalence preserves composition. -/
theorem occupationConjugate_comp
    (b : Module.Basis Mode ℂ 𝓗₁)
    (A B : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) :
    AlgebraicFock.occupationConjugate b (A.comp B) =
      (AlgebraicFock.occupationConjugate b A).comp (AlgebraicFock.occupationConjugate b B) := by
  apply LinearMap.ext
  intro Ψ
  apply (AlgebraicFock.occupationEquiv b).injective
  calc
    AlgebraicFock.occupationEquiv b (AlgebraicFock.occupationConjugate b (A.comp B) Ψ) =
        (A.comp B) (AlgebraicFock.occupationEquiv b Ψ) :=
      AlgebraicFock.occupationEquiv_occupationConjugate_apply b (A.comp B) Ψ
    _ = A (B (AlgebraicFock.occupationEquiv b Ψ)) := rfl
    _ = A (AlgebraicFock.occupationEquiv b (AlgebraicFock.occupationConjugate b B Ψ)) := by
      rw [AlgebraicFock.occupationEquiv_occupationConjugate_apply]
    _ = AlgebraicFock.occupationEquiv b
        (AlgebraicFock.occupationConjugate b A (AlgebraicFock.occupationConjugate b B Ψ)) :=
      (AlgebraicFock.occupationEquiv_occupationConjugate_apply b A
        (AlgebraicFock.occupationConjugate b B Ψ)).symm

/-- Exterior creation by a basis vector conjugates to occupation creation in the corresponding
mode. -/
theorem occupationConjugate_create
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    AlgebraicFock.occupationConjugate b (AlgebraicFock.create 𝓗₁ (b i)) =
      SecondQuantization.Fermionic.create i := by
  apply LinearMap.ext
  intro Ψ
  apply (AlgebraicFock.occupationEquiv b).injective
  rw [AlgebraicFock.occupationEquiv_occupationConjugate_apply]
  have h := LinearMap.congr_fun (AlgebraicFock.occupationEquiv_create b i) Ψ
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
        (AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y)) =
      (SecondQuantization.Fermionic.create x).comp
        (SecondQuantization.Fermionic.annihilate y) := by
  change AlgebraicFock.occupationConjugate (latticeBasis (Site := Site))
      (AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y)) = _
  rw [dGamma_matrixUnit, occupationConjugate_comp]
  rw [← latticeBasis_apply_eq_latticeKet (Site := Site) x,
    ← latticeBasis_coord_eq_latticeCoordinateDual (Site := Site) y]
  rw [occupationConjugate_create]
  change
    (SecondQuantization.Fermionic.create x).comp
        (AlgebraicFock.occupationAnnihilateFromField (latticeBasis (Site := Site)) y) = _
  rw [AlgebraicFock.occupationAnnihilateFromField_eq_annihilate]

section Finite

variable [Fintype Site]

/-- Bounded finite-Hilbert realization of a second-quantized one-particle matrix unit. -/
noncomputable def boundedDgammaMatrixUnit (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y))

/-- The bounded matrix-unit realization is the finite-Hilbert creation-annihilation bilinear. -/
theorem boundedDgammaMatrixUnit_eq_create_comp_annihilate (x y : Site) :
    boundedDgammaMatrixUnit x y =
      (finiteHilbertCreate x).comp (finiteHilbertAnnihilate y) := by
  change Common.finiteHilbertOperator
      (occupationOperator (AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y))) = _
  rw [occupationOperator_dGamma_matrixUnit, Common.finiteHilbertOperator_comp]
  rfl

/-- On the one-particle occupation basis, the bounded second-quantized matrix unit sends the
singleton state at `y` to the singleton state at `x`. -/
@[simp]
theorem boundedDgammaMatrixUnit_apply_singleton (x y : Site) :
    boundedDgammaMatrixUnit x y
        (Common.finiteHilbertBasisState ({y} : Occupation Site)) =
      Common.finiteHilbertBasisState ({x} : Occupation Site) := by
  rw [boundedDgammaMatrixUnit_eq_create_comp_annihilate]
  change finiteHilbertCreate x
      (finiteHilbertAnnihilate y
        (Common.finiteHilbertBasisState ({y} : Occupation Site))) = _
  have hy : fermionSign y ({y} : Occupation Site) = 1 := by
    unfold fermionSign
    have hfilter : {z ∈ ({y} : Finset Site) | z < y} = ∅ := by
      ext z
      constructor
      · intro hz
        have hzmem : z ∈ ({y} : Finset Site) := (Finset.mem_filter.mp hz).1
        have hzlt : z < y := (Finset.mem_filter.mp hz).2
        have hzy : z = y := Finset.mem_singleton.mp hzmem
        subst z
        exact (lt_irrefl y hzlt).elim
      · intro hz
        exact False.elim ((Finset.notMem_empty z) hz)
    rw [hfilter]
    simp only [Finset.card_empty, pow_zero]
  rw [finiteHilbertAnnihilate_basisState_of_mem (by simp), hy]
  simp only [Int.cast_one, one_smul]
  rw [finiteHilbertCreate_basisState_of_not_mem (by simp [removeOccupation])]
  simp [fermionSign, removeOccupation, insertOccupation]

/-- A bounded second-quantized matrix unit kills a one-particle singleton state whose occupied site
is not its source site. -/
@[simp]
theorem boundedDgammaMatrixUnit_apply_singleton_of_ne (x y z : Site) (h : z ≠ y) :
    boundedDgammaMatrixUnit x y
        (Common.finiteHilbertBasisState ({z} : Occupation Site)) = 0 := by
  rw [boundedDgammaMatrixUnit_eq_create_comp_annihilate]
  change finiteHilbertCreate x
      (finiteHilbertAnnihilate y
        (Common.finiteHilbertBasisState ({z} : Occupation Site))) = 0
  rw [finiteHilbertAnnihilate_basisState_of_not_mem]
  · exact map_zero _
  · simpa [eq_comm] using h

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
end Lattice
end Fermionic
end SecondQuantization
