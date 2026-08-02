import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsDensityOperator

set_option linter.style.header false

/-!
# The canonical free-fermion Gibbs density operator

The finite free-fermion thermal state is the canonical finite Gibbs density operator specialized to
`fermionEnergy ε`. This gives the E4 migration a genuine density-state object before the temporary
occupation-coordinate `freeGibbsExpectation` API is removed.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory.TraceClass

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The canonical finite free-fermion Gibbs state. -/
noncomputable def freeGibbsDensityOperator (ε : Mode → ℝ) (β : ℝ) :
    DensityOperator (Common.FiniteHilbertFock (Occupation Mode)) :=
  Common.finiteGibbsDensityOperator (fermionEnergy ε) β

omit [DecidableEq Mode] [LinearOrder Mode] in
/-- The free Gibbs density operator acts diagonally in the occupation basis. -/
@[simp]
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
    (ε : Mode → ℝ) (β : ℝ) (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperator A) =
      Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  rw [freeGibbsDensityOperator, Common.finiteGibbsExpectation,
    Common.finiteGibbsExpectationLinearMap, LinearMap.comp_apply,
    Common.finiteHilbertOperatorLinearMap_apply]
  rfl

omit [LinearOrder Mode] in
/-- Temporary E4 bridge from the canonical free Gibbs density state to the legacy coordinate
presentation. This theorem is removed together with `freeGibbsExpectation` after its callers
migrate. -/
theorem freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperator A) =
      freeGibbsExpectation ε β A := by
  rw [freeGibbsExpectation_eq_finiteGibbsExpectation]
  exact freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation ε β A

omit [LinearOrder Mode] in
/-- The canonical free Gibbs density-state expectation commutes with the finite algebraic operator
interval integral. This is the analytic bridge needed to migrate the Dyson induction without
exposing the temporary occupation-coordinate expectation at its call sites. -/
theorem freeGibbsDensityOperator_expectation_operatorIntervalIntegral
    (ε : Mode → ℝ) (β : ℝ)
    (F : ℝ → FockSpace Mode →ₗ[ℂ] FockSpace Mode) (a b : ℝ)
    (hF : ∀ n : Occupation Mode, IntervalIntegrable
      (fun τ => Common.matrixCoeff (F τ) n n) MeasureTheory.volume a b) :
    (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator (Common.operatorIntervalIntegral F a b)) =
      ∫ τ in a..b,
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator (F τ)) := by
  simp_rw [freeGibbsDensityOperator_expectation_eq_freeGibbsExpectation]
  exact freeGibbsExpectation_operatorIntervalIntegral ε β F a b hF

end Fermionic
end SecondQuantization
