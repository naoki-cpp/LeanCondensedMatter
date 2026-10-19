import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
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

/-- The basis-independent lattice charge becomes the occupation number operator under the
canonical one-particle site basis, for any site type. -/
private theorem occupationConjugate_siteChargeDensity (q : ℂ) (x : Site) :
    AlgebraicFock.occupationConjugate
        (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))
        (siteChargeDensity q x) = q • numberOperator x := by
  classical
  unfold siteChargeDensity
  rw [map_smul]
  change q • AlgebraicFock.occupationConjugate
      (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))
      (AlgebraicFock.dGamma ((Site →₀ ℂ)) (matrixUnit x x)) = _
  rw [dGamma_matrixUnit]
  have hConj := map_mul
    (AlgebraicFock.occupationConjugate
      (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ)))
    (AlgebraicFock.create ((Site →₀ ℂ)) (latticeKet x))
    (AlgebraicFock.annihilateDual ((Site →₀ ℂ)) (Finsupp.lapply x))
  simp only [Module.End.mul_eq_comp] at hConj
  rw [hConj]
  have hx : (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ)) x =
      latticeKet x := rfl
  have hcoord :
      (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ)).coord x =
        (Finsupp.lapply x : Module.Dual ℂ (Site →₀ ℂ)) := by
    ext ψ
    rfl
  rw [← hx, ← hcoord, AlgebraicFock.occupationConjugate_create,
    AlgebraicFock.occupationConjugate_annihilateDual]
  rfl

/-- The completed local charge realizes the original algebraic lattice charge on the dense
algebraic core. In particular, no `Fintype Site` assumption is needed. -/
theorem completedSiteChargeDensity_comp_algebraicToCompleted (q : ℂ) (x : Site) :
    (q • completedNumberOperator x).toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp
        (AlgebraicFock.occupationConjugate
          (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))
          (siteChargeDensity q x)) := by
  rw [occupationConjugate_siteChargeDensity]
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
