import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Recursion

set_option linter.style.header false

/-!
# The general finite-temperature Bloch–de Dominicis theorem

The arbitrary-length pairing induction now depends only on
`ExpectationPairingRecursion`: normalization of the empty product, stability of admissibility under
erasing a pair, and the KMS/exchange first-pair recurrence.

The canonical finite Gibbs density-state implementation is provided separately by
`GibbsExpectation/Recursion.lean`.  Consequently, the induction in this file has no direct knowledge
of occupation-basis sums, trace ratios, or the proof of KMS rotation.  A future summability-aware
bosonic expectation can instantiate the same recursion contract without a false finite-configuration
assumption.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- **The general finite-temperature Bloch–de Dominicis theorem.** -/
theorem finiteGibbsExpectation_prodComp_eq_sum_pairing (s : Statistics)
    (energy : Config → ℝ) (β : ℝ)
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0) :
    ∀ (n : ℕ) (C : Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
      (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ),
      (∀ i, heisenbergEvolve energy (-β) (C i) = Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i) →
      (∀ i j, i ≠ j → zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
        c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) →
      (∀ i, (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q i * β : ℝ) : ℂ) ≠ 0) →
      finiteGibbsExpectation energy β (prodComp (List.ofFn C)) =
        ∑ pairing : Pairing n,
          pairing.weight s *
            ∏ pr ∈ pairing.pairs,
              finiteGibbsExpectation energy β ((C pr.1).comp (C pr.2)) := by
  intro n C q c hC hcomm hne
  exact (finiteGibbsExpectationRecursion s energy β hZ).expectation_eq_sum_pairing
    n C ⟨q, c, hC, hcomm, hne⟩

end BlochDeDominicis
end Common
end SecondQuantization
