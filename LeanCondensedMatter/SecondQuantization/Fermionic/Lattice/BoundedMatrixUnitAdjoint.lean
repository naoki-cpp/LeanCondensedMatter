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
  change Common.finiteHilbertOperatorAlgEquiv
      (AlgebraicFock.occupationConjugate (latticeBasis (Site := Site))
        (AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y))) = _
  rw [dGamma_matrixUnit]
  have hConj := map_mul
    (AlgebraicFock.occupationConjugate (latticeBasis (Site := Site)))
    (AlgebraicFock.create (LatticeState Site) (latticeKet x))
    (AlgebraicFock.annihilateDual (LatticeState Site) (Finsupp.lapply y))
  simp only [Module.End.mul_eq_comp] at hConj
  rw [hConj]
  have hx : latticeBasis (Site := Site) x = latticeKet x := rfl
  rw [← hx, ← latticeBasis_coord_eq_lapply (Site := Site) y]
  rw [AlgebraicFock.occupationConjugate_create,
    AlgebraicFock.occupationConjugate_annihilateDual,
    finiteHilbertCreate, finiteHilbertAnnihilate]
  simpa only [← Module.End.mul_eq_comp, ← ContinuousLinearMap.mul_def] using
    map_mul (Common.finiteHilbertOperatorAlgEquiv (Config := Occupation Site))
      (create x) (annihilate y)

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
