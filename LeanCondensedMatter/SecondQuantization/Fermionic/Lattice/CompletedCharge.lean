import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core

set_option linter.style.header false

/-!
# Local lattice charge on completed fermionic Fock space

A one-site charge density is a scalar multiple of the occupation projection. Unlike the
finite-Hilbert transport of arbitrary algebraic Fock endomorphisms, this bounded realization
works for arbitrary site types. The occupation/exterior-algebra bridge identifies it with
the original basis-independent lattice charge density on the dense algebraic core.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

variable {Site : Type*} [LinearOrder Site]

/-- The completed local charge realizes the original algebraic lattice charge on the dense
algebraic core. In particular, no `Fintype Site` assumption is needed. -/
theorem completedSiteChargeDensity_comp_algebraicToCompleted (q : ℂ) (x : Site) :
    (q • completedNumberOperator x).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp
        (AlgebraicFock.occupationConjugate
          (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))
          (siteChargeDensity q x)) := by
  rw [siteChargeDensity, map_smul, siteProjector,
    occupationConjugate_dGamma_matrixUnit]
  change (q • completedNumberOperator x).toLinearMap.comp algebraicToCompleted =
    algebraicToCompleted.comp (q • numberOperator x)
  apply Common.linearMap_ext_basisState
  intro n
  change (q • completedNumberOperator x) (algebraicToCompleted (basisState n)) =
    algebraicToCompleted ((q • numberOperator x) (basisState n))
  rw [smul_apply, LinearMap.smul_apply, map_smul]
  have hcore :
      completedNumberOperator x (algebraicToCompleted (basisState n)) =
        algebraicToCompleted (numberOperator x (basisState n)) := by
    have h := LinearMap.congr_fun
      (completedNumberOperator_comp_algebraicToCompleted x) (basisState n)
    change completedNumberOperator x (algebraicToCompleted (basisState n)) =
      algebraicToCompleted (numberOperator x (basisState n)) at h
    exact h
  rw [hcore]

end
end Lattice
end Fermionic
end SecondQuantization
