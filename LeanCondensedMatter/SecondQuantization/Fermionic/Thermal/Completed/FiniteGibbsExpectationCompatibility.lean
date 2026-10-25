import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteCompletedGibbsCompatibility

set_option linter.style.header false

/-!
# Finite/completed fermionic Gibbs expectation compatibility

For finite fermionic mode types, the density-state expectation agrees with
the completed Gibbs expectation of a bounded operator extending an algebraic
observable. The proof specializes the statistics-independent finite/completed
Gibbs expectation bridge to the shifted fermionic energy `ε - μ`.
This does not identify arbitrary bounded completed operators with algebraic-Fock
endomorphisms in infinite modes.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- Transport a finite free-fermion expectation to the completed normal grand-canonical
Gibbs state whenever the bounded completed operator extends the algebraic observable.
The chemical potential is explicit, and finite modes enter solely through this bridge. -/
theorem freeGibbsExpectation_eq_completed_of_algebraicCore
    (ε : Mode → ℝ) (β μ : ℝ)
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
    (T : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
    (hcore : T.toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp A) :
    (freeGibbsDensityOperator (fun i => ε i - μ) β).expectation
      (Common.finiteHilbertOperatorAlgEquiv A) =
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode)
      ε β μ (eigenbasisGibbsSummable_of_finite
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)).expectation T := by
  have hE :
      Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
        fermionEnergy (fun i => ε i - μ) := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  simpa [Common.grandCanonicalGibbsDensityOperator,
    freeGibbsDensityOperator, hE] using
    (Common.finiteGibbsExpectation_eq_completed_of_algebraicCore
      (Config := Occupation Mode) (fermionEnergy (fun i => ε i - μ)) β A T hcore)


end
end Fermionic
end SecondQuantization
