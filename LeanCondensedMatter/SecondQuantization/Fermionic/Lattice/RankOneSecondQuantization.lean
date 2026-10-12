import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.RankOne
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice

set_option linter.style.header false

/-!
# Lattice rank-one second-quantization adapter

This module specializes the basis-independent algebraic rank-one theorem to lattice matrix units.
The generic `dGamma_dualRankOne` theorem is owned upstream by `Fermionic.AlgebraicFock`, with the
rank-one one-particle map represented directly by Mathlib's `LinearMap.smulRight`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

variable {Site : Type*}

/-- The second quantization of a lattice matrix unit factors into creation and annihilation fields. -/
theorem dGamma_matrixUnit (x y : Site) :
    AlgebraicFock.dGamma ((Site →₀ ℂ)) (matrixUnit x y) =
      (AlgebraicFock.create ((Site →₀ ℂ)) (latticeKet x)).comp
        (AlgebraicFock.annihilateDual ((Site →₀ ℂ)) (Finsupp.lapply y)) := by
  have hRankOne :
      (Finsupp.lapply y : Module.Dual ℂ ((Site →₀ ℂ))).smulRight (latticeKet x) =
        matrixUnit x y := by
    apply LinearMap.ext
    intro ψ
    rw [matrixUnit_apply]
    simp [latticeKet]
  rw [← hRankOne]
  exact AlgebraicFock.dGamma_dualRankOne
    ((Site →₀ ℂ)) (latticeKet x) (Finsupp.lapply y)

end
end Lattice
end Fermionic
end SecondQuantization
