import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator

set_option linter.style.header false

/-!
# The canonical free-fermion Gibbs density operator

The finite free-fermion thermal state is the canonical finite Gibbs density operator specialized to
`fermionEnergy ε`. This module records its occupation-basis action and identifies density-operator
expectations of transported algebraic observables with the canonical finite Gibbs expectation.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The canonical finite free-fermion Gibbs state. -/
noncomputable def freeGibbsDensityOperator (ε : Mode → ℝ) (β : ℝ) :
    DensityOperator (Common.FiniteHilbertFock (Occupation Mode)) :=
  Common.finiteGibbsDensityOperator (fermionEnergy ε) β

omit [LinearOrder Mode] in
/-- The free Gibbs density operator acts diagonally in the occupation basis. -/
theorem freeGibbsDensityOperator_apply_basis (ε : Mode → ℝ) (β : ℝ)
    (n : Occupation Mode) :
    (freeGibbsDensityOperator ε β).op (Common.finiteHilbertBasisState n) =
      (((Common.finitePartitionFunction (fermionEnergy ε) β)⁻¹ *
          Common.finiteBoltzmannWeight (fermionEnergy ε) β n : ℝ) : ℂ) •
        Common.finiteHilbertBasisState n := by
  simpa [freeGibbsDensityOperator] using
    Common.finiteGibbsDensityOperator_apply_basis (fermionEnergy ε) β n

omit [LinearOrder Mode] in
/-- Evaluating the free Gibbs density state on a transported algebraic Fock operator is the
canonical finite Gibbs expectation at `fermionEnergy ε`. -/
theorem freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperator A) =
      Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  rw [freeGibbsDensityOperator, Common.finiteGibbsExpectation,
    Common.finiteGibbsExpectationLinearMap, LinearMap.comp_apply,
    Common.finiteHilbertOperatorLinearMap_apply]
  rfl

end Fermionic
end SecondQuantization
