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

/-- A lattice matrix unit is the corresponding algebraic rank-one map. -/
theorem dualRankOne_latticeKet_lapply (x y : Site) :
    AlgebraicFock.dualRankOne (LatticeState Site) (latticeKet x) (Finsupp.lapply y) =
      matrixUnit x y := by
  apply LinearMap.ext
  intro ψ
  rw [AlgebraicFock.dualRankOne_apply, matrixUnit_apply]
  simp [latticeKet]

/-- The second quantization of a lattice matrix unit factors into creation and annihilation fields. -/
theorem dGamma_matrixUnit (x y : Site) :
    AlgebraicFock.dGamma (LatticeState Site) (matrixUnit x y) =
      (AlgebraicFock.create (LatticeState Site) (latticeKet x)).comp
        (AlgebraicFock.annihilateDual (LatticeState Site) (Finsupp.lapply y)) := by
  rw [← dualRankOne_latticeKet_lapply]
  exact AlgebraicFock.dGamma_dualRankOne
    (LatticeState Site) (latticeKet x) (Finsupp.lapply y)

end
end Lattice
end Fermionic
end SecondQuantization
