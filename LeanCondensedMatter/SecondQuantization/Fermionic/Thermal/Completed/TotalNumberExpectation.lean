import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Completed free-fermion total-number Gibbs expectation

The completed total-number operator is genuinely unbounded, so it is not passed to
`DensityOperator.expectation`, whose observable argument is bounded. Instead its Gibbs expectation
is the absolutely convergent spectral series of its occupation-basis eigenvalues, under both
existence of the completed free Gibbs state and explicit total-number integrability.

The operator and its maximal domain remain owned by `Fermionic.CompletedSpace.Diagonal`. This module
owns only the thermal integrability condition and expectation for that concrete observable. Generic
pure-point energy expectations remain in `QuantumTheory.Gibbs.PurePointExpectation`; no parallel
public arbitrary-diagonal expectation API is introduced here.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*}

/-- Integrability condition for the completed total particle-number operator in an existing free
Gibbs state. The `hsum` argument records the state-existence hypothesis explicitly at the API
boundary. -/
def CompletedFreeTotalNumberIntegrable
    (ε : Mode → ℝ) (β : ℝ) (_hsum : PurePointGibbsSummable (fermionEnergy ε) β) : Prop :=
  Summable fun n : Occupation Mode =>
    ‖purePointGibbsProbability (fermionEnergy ε) β n * (particleNumber n : ℝ)‖

/-- Thermal expectation of the completed total particle-number operator, defined by its real
occupation-basis spectral series for an existing completed free Gibbs state. -/
noncomputable def completedFreeTotalNumberExpectation
    (ε : Mode → ℝ) (β : ℝ) (_hsum : PurePointGibbsSummable (fermionEnergy ε) β) : ℝ :=
  ∑' n : Occupation Mode,
    purePointGibbsProbability (fermionEnergy ε) β n * (particleNumber n : ℝ)

/-- Under the explicit number-integrability hypothesis, the total particle-number expectation is
represented by an absolutely convergent occupation-basis series. -/
theorem hasSum_completedFreeTotalNumberExpectation
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (hint : CompletedFreeTotalNumberIntegrable ε β hsum) :
    HasSum
      (fun n : Occupation Mode =>
        purePointGibbsProbability (fermionEnergy ε) β n * (particleNumber n : ℝ))
      (completedFreeTotalNumberExpectation ε β hsum) := by
  exact (Summable.of_norm hint).hasSum

/-- The completed free total-number expectation is nonnegative. -/
theorem completedFreeTotalNumberExpectation_nonneg
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    0 ≤ completedFreeTotalNumberExpectation ε β hsum := by
  unfold completedFreeTotalNumberExpectation
  exact tsum_nonneg fun n =>
    mul_nonneg (purePointGibbsProbability_nonneg (fermionEnergy ε) β hsum n)
      (Nat.cast_nonneg (particleNumber n))

/-- On each occupation basis state, the diagonal matrix element of the composed completed Gibbs
density operator and total-number operator is the corresponding Gibbs probability times particle
number. -/
theorem completedFreeGibbsDensityOperator_totalNumber_diagonalTerm
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (n : Occupation Mode) :
    inner ℂ (completedBasisState n)
        ((completedFreeGibbsDensityOperator ε β hsum).op
          (completedTotalNumberOperator
            ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩)) =
      (purePointGibbsProbability (fermionEnergy ε) β n *
        (particleNumber n : ℝ) : ℝ) := by
  rw [completedTotalNumberOperator_basisState, map_smul,
    completedFreeGibbsDensityOperator_apply_basis]
  simp

/-- The diagonal matrix elements of the actual completed Gibbs density operator composed with the
completed total-number operator sum to the real spectral expectation. -/
theorem hasSum_completedFreeGibbsDensityOperator_totalNumber_diagonal
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (hint : CompletedFreeTotalNumberIntegrable ε β hsum) :
    HasSum
      (fun n : Occupation Mode =>
        inner ℂ (completedBasisState n)
          ((completedFreeGibbsDensityOperator ε β hsum).op
            (completedTotalNumberOperator
              ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩)))
      (completedFreeTotalNumberExpectation ε β hsum : ℂ) := by
  simpa [completedFreeGibbsDensityOperator_totalNumber_diagonalTerm] using
    (hasSum_completedFreeTotalNumberExpectation ε β hsum hint).mapL Complex.ofRealCLM

end
end Fermionic
end SecondQuantization
