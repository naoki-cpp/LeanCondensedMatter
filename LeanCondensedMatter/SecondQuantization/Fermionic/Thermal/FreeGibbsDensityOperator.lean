import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# The full-Fock free-fermion Gibbs density operator

The finite free-fermion thermal state is the generic finite pure-point Gibbs density operator
specialized to the occupation basis and `fermionEnergy ε`. This module records its occupation-basis
action and identifies density-operator expectations of transported algebraic observables with the
canonical finite Gibbs expectation adapter.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The finite full-occupation-Fock free-fermion Gibbs state, without a fixed total
particle number. It is not the fixed-`N` canonical ensemble. -/
noncomputable def freeGibbsDensityOperator (ε : Mode → ℝ) (β : ℝ) :
    DensityOperator (Common.FiniteHilbertFock (Occupation Mode)) :=
  eigenbasisGibbsDensityOperator
    (Common.finiteHilbertBasis (Config := Occupation Mode)) (fermionEnergy ε) β
    (eigenbasisGibbsSummable_of_finite (fermionEnergy ε) β)

omit [LinearOrder Mode] in
/-- The free Gibbs density operator acts diagonally in the occupation basis. -/
theorem freeGibbsDensityOperator_apply_basis (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    (freeGibbsDensityOperator ε β).op (Common.finiteHilbertBasisState n) =
      (eigenbasisGibbsProbability (fermionEnergy ε) β n : ℂ) •
        Common.finiteHilbertBasisState n := by
  simpa [freeGibbsDensityOperator] using
    eigenbasisGibbsDensityOperator_apply_basis
      (Common.finiteHilbertBasis (Config := Occupation Mode)) (fermionEnergy ε) β
      (eigenbasisGibbsSummable_of_finite (fermionEnergy ε) β) n

omit [LinearOrder Mode] in
/-- Evaluating the free Gibbs density state on a transported algebraic Fock operator is the
canonical finite Gibbs expectation at `fermionEnergy ε`. -/
theorem freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperatorAlgEquiv A) =
      Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  rw [freeGibbsDensityOperator, Common.finiteGibbsExpectation,
    Common.finiteGibbsExpectationLinearMap, LinearMap.comp_apply]
  rfl

end Fermionic
end SecondQuantization
