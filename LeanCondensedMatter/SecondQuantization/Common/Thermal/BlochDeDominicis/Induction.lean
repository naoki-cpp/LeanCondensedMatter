import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Recursion

set_option linter.style.header false

/-!
# The general finite-temperature Bloch–de Dominicis theorem

The arbitrary-length pairing induction now depends only on
`ExpectationPairingRecursion`: normalization of the empty product, stability of admissibility under
erasing a pair, and the KMS/exchange first-pair recurrence.

The canonical finite Gibbs density-state implementation is provided separately by
`GibbsExpectation/Recursion.lean`. Consequently, the induction in this file has no direct knowledge
of occupation-basis sums, trace ratios, or the proof of KMS rotation. A future summability-aware
bosonic expectation can instantiate the same recursion contract without a false finite-configuration
assumption.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- **The general finite-temperature Bloch–de Dominicis theorem.** The original linked-diagram
and finite-temperature pairing development is C. Bloch and C. de Dominicis, *Nuclear Physics*
**7**, 459–479 (1958),
[doi:10.1016/0029-5582(58)90285-2](https://doi.org/10.1016/0029-5582(58)90285-2).
For the unified bosonic/fermionic thermal Wick argument motivating this pairing formula, see M. Gaudin, *Nuclear
Physics* **15**, 89–91 (1960),
[doi:10.1016/0029-5582(60)90285-6](https://doi.org/10.1016/0029-5582(60)90285-6). This theorem is
the finite-Gibbs recursion specialization described above; it does not claim the infinite-volume
or interacting-state generality of the original diagrammatic development. -/
theorem finiteGibbsExpectation_prod_eq_sum_pairing (s : Statistics)
    (energy : Config → ℝ) (β : ℝ) :
    ∀ (n : ℕ) (C : Fin (2 * n) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
      (q : Fin (2 * n) → ℝ) (c : Fin (2 * n) → Fin (2 * n) → ℂ),
      (∀ i, heisenbergEvolve energy (-β) (C i) = Complex.exp ((q i * (-β) : ℝ) : ℂ) • C i) →
      (∀ i j, i ≠ j → ScalarExchange.zetaCommutator (s.zetaInt : ℂ) (C i) (C j) =
        c i j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) →
      (∀ i, (1 : ℂ) - (s.zetaInt : ℂ) * Complex.exp ((q i * β : ℝ) : ℂ) ≠ 0) →
      finiteGibbsExpectation energy β (List.prod (List.ofFn C)) =
        ∑ pairing : Pairing n,
          pairing.weight s *
            ∏ pr ∈ pairing.pairs,
              finiteGibbsExpectation energy β ((C pr.1).comp (C pr.2)) := by
  intro n C q c hC hcomm hne
  exact (finiteGibbsExpectationRecursion s energy β).bloch_de_dominicis
    n C ⟨q, c, hC, hcomm, hne⟩

end BlochDeDominicis
end Common
end SecondQuantization
