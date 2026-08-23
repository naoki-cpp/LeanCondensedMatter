import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.RankOne
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice

set_option linter.style.header false

/-!
# Lattice rank-one second-quantization adapter

This module specializes the basis-independent algebraic rank-one theorem to lattice matrix units.
The generic `dualRankOne` and `dGamma_dualRankOne` declarations are owned upstream by
`Fermionic.AlgebraicFock`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

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
    AlgebraicFock.dualRankOne (LatticeState Site) (latticeKet x) (latticeCoordinateDual y) =
      matrixUnit x y := by
  apply LinearMap.ext
  intro ψ
  change Finsupp.single x (ψ y) = Finsupp.single x (ψ y)
  rfl

/-- The second quantization of a lattice matrix unit factors into creation and annihilation fields. -/
theorem dGamma_matrixUnit (x y : Site) :
    AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y) =
      (AlgebraicFock.create (LatticeState Site) (latticeKet x)).comp
        (AlgebraicFock.annihilateDual (LatticeState Site) (latticeCoordinateDual y)) := by
  rw [← dualRankOne_latticeKet_latticeCoordinateDual]
  exact AlgebraicFock.dGamma_dualRankOne
    (LatticeState Site) (latticeKet x) (latticeCoordinateDual y)

end
end Lattice
end Fermionic
end SecondQuantization
