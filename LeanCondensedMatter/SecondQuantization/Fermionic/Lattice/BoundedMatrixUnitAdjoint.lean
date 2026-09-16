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

variable {Site : Type*}

private theorem latticeBasis_coord_eq_lapply (y : Site) :
    (latticeBasis (Site := Site)).coord y =
      (Finsupp.lapply y : Module.Dual ℂ (LatticeState Site)) := by
  apply LinearMap.ext
  intro ψ
  change ψ y = ψ y
  rfl

variable [LinearOrder Site]

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
      (AlgebraicFock.occupationConjugate (latticeBasis (Site := Site))
        (AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y))) = _
  rw [dGamma_matrixUnit, AlgebraicFock.occupationConjugate_comp]
  have hx : latticeBasis (Site := Site) x = latticeKet x := rfl
  rw [← hx, ← latticeBasis_coord_eq_lapply (Site := Site) y]
  rw [AlgebraicFock.occupationConjugate_create,
    AlgebraicFock.occupationConjugate_annihilateDual,
    Common.finiteHilbertOperator_comp]
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
    calc
      fermionSign y ({y} : Occupation Site) =
          fermionSign y (insertOccupation y (vacuum : Occupation Site)) := by
        simp [insertOccupation, vacuum]
      _ = fermionSign y (vacuum : Occupation Site) :=
        fermionSign_insertOccupation_of_not_lt (lt_irrefl y)
      _ = 1 := fermionSign_vacuum y
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
