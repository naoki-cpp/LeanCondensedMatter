import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Completed free-fermion total-number Gibbs expectation

The completed total-number operator is genuinely unbounded, so it is not passed to
`DensityOperator.expectation`, whose observable argument is bounded. Instead its Gibbs expectation
is the absolutely convergent spectral series of its occupation-basis eigenvalues.

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

/-- Integrability condition for the completed total particle-number operator in the free Gibbs
state. -/
def CompletedFreeTotalNumberIntegrable (ε : Mode → ℝ) (β : ℝ) : Prop :=
  Summable fun n : Occupation Mode =>
    ‖purePointGibbsProbability (fermionEnergy ε) β n * (particleNumber n : ℝ)‖

/-- Thermal expectation of the completed total particle-number operator, defined by its real
occupation-basis spectral series. -/
noncomputable def completedFreeTotalNumberExpectation (ε : Mode → ℝ) (β : ℝ) : ℝ :=
  ∑' n : Occupation Mode,
    purePointGibbsProbability (fermionEnergy ε) β n * (particleNumber n : ℝ)

/-- Under the explicit number-integrability hypothesis, the total particle-number expectation is
represented by an absolutely convergent occupation-basis series. -/
theorem hasSum_completedFreeTotalNumberExpectation
    (ε : Mode → ℝ) (β : ℝ) (hint : CompletedFreeTotalNumberIntegrable ε β) :
    HasSum
      (fun n : Occupation Mode =>
        purePointGibbsProbability (fermionEnergy ε) β n * (particleNumber n : ℝ))
      (completedFreeTotalNumberExpectation ε β) := by
  exact (Summable.of_norm hint).hasSum

/-- The completed free total-number expectation is nonnegative whenever the Gibbs state exists. -/
theorem completedFreeTotalNumberExpectation_nonneg
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    0 ≤ completedFreeTotalNumberExpectation ε β := by
  unfold completedFreeTotalNumberExpectation
  exact tsum_nonneg fun n =>
    mul_nonneg (purePointGibbsProbability_nonneg (fermionEnergy ε) β hsum n)
      (Nat.cast_nonneg (particleNumber n))

/-- The spectral term used in the total-number expectation is the diagonal matrix element of the
actual completed total-number operator on the occupation basis. -/
theorem completedFreeTotalNumberOperator_diagonalTerm
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
        inner ℂ (completedBasisState n)
          (completedTotalNumberOperator
            ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩) =
      (purePointGibbsProbability (fermionEnergy ε) β n *
        (particleNumber n : ℝ) : ℝ) := by
  rw [completedTotalNumberOperator_basisState]
  simp

/-- The complex diagonal-matrix-element series of the completed total-number operator has the same
sum as the real spectral expectation. -/
theorem hasSum_completedFreeTotalNumberOperator_diagonal
    (ε : Mode → ℝ) (β : ℝ) (hint : CompletedFreeTotalNumberIntegrable ε β) :
    HasSum
      (fun n : Occupation Mode =>
        (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) *
          inner ℂ (completedBasisState n)
            (completedTotalNumberOperator
              ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩))
      (completedFreeTotalNumberExpectation ε β : ℂ) := by
  simpa [completedFreeTotalNumberOperator_diagonalTerm] using
    (hasSum_completedFreeTotalNumberExpectation ε β hint).mapL Complex.ofRealCLM

end
end Fermionic
end SecondQuantization
