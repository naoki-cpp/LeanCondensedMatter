import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal

set_option linter.style.header false

/-!
# Completed free-fermion total-number Gibbs expectation

The completed total-number operator is genuinely unbounded, so it is not passed to
`DensityOperator.expectation`, whose observable argument is bounded. Instead its Gibbs expectation
is the spectral series of its occupation-basis eigenvalues. Absolute convergence is tracked by an
explicit total-number integrability condition; existence of the completed free Gibbs density state
is required only by the bridge back to the density operator.

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

/-- Integrability condition for the completed total particle-number spectral series. State
existence is deliberately not part of this scalar summability predicate. -/
def CompletedFreeTotalNumberIntegrable
    (ε : Mode → ℝ) (β : ℝ) : Prop :=
  Summable fun n : Occupation Mode =>
    ‖purePointGibbsProbability (fermionEnergy ε) β n * (particleNumber n : ℝ)‖

/-- Thermal expectation of the completed total particle-number operator, defined by its real
occupation-basis spectral series. -/
noncomputable def completedFreeTotalNumberExpectation
    (ε : Mode → ℝ) (β : ℝ) : ℝ :=
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

/-- The completed free total-number expectation is nonnegative. -/
theorem completedFreeTotalNumberExpectation_nonneg
    (ε : Mode → ℝ) (β : ℝ) :
    0 ≤ completedFreeTotalNumberExpectation ε β := by
  unfold completedFreeTotalNumberExpectation
  exact tsum_nonneg fun n =>
    mul_nonneg (purePointGibbsProbability_nonneg (fermionEnergy ε) β n)
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
  have hnorm : ‖completedBasisState n‖ = 1 := by
    rw [← completedOccupationHilbertBasis_apply]
    exact (completedOccupationHilbertBasis (Mode := Mode)).orthonormal.norm_eq_one n
  rw [completedTotalNumberOperator_basisState, map_smul,
    completedFreeGibbsDensityOperator_apply_basis, inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hnorm]
  norm_num
  ring

/-- The diagonal matrix elements of the actual completed Gibbs density operator composed with the
completed total-number operator sum to the real spectral expectation. -/
theorem hasSum_completedFreeGibbsDensityOperator_totalNumber_diagonal
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β)
    (hint : CompletedFreeTotalNumberIntegrable ε β) :
    HasSum
      (fun n : Occupation Mode =>
        inner ℂ (completedBasisState n)
          ((completedFreeGibbsDensityOperator ε β hsum).op
            (completedTotalNumberOperator
              ⟨completedBasisState n, completedBasisState_mem_completedTotalNumberDomain n⟩)))
      (completedFreeTotalNumberExpectation ε β : ℂ) := by
  have hcast :=
    (hasSum_completedFreeTotalNumberExpectation ε β hint).mapL Complex.ofRealCLM
  simp only [Complex.ofRealCLM_apply] at hcast
  simpa only [completedFreeGibbsDensityOperator_totalNumber_diagonalTerm] using hcast

end
end Fermionic
end SecondQuantization
