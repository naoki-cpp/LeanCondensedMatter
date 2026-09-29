---
status: accepted
---

# Keep thermal pairing recursion independent of state construction

Represent the finite-temperature Bloch–de Dominicis expansion—a pairing sum for ordered thermal expectations—through `ExpectationPairingRecursion`: it takes an ordered expectation, an admissibility predicate and values for admissible operator pairs, empty-pairing normalization, and the recurrence that splits off the pair containing the first operator and reindexes the remaining positions. Each thermal representation supplies its own Gibbs expectation, KMS/exchange identity, and analytic or domain hypotheses, since the generic induction proves none of those representation-specific facts.

Keep `Fermionic.Thermal` APIs tied to actual Gibbs/KMS or thermal-expectation semantics: derive physical Green-function contractions from the BDD two-point API, and keep arbitrary complex-weight moments/cumulants and one-consumer coordinate bridges generic or private until they have a real thermal contract.

Share the finite scalar-exchange recurrence in `Analysis.ScalarExchange` under only its associative unital complex-algebra and scalar-exchange assumptions; keep CAR/CCR realization and the decomposition that removes the pair containing the first operator and reindexes the remaining positions at the representation-specific consumers.

Evidence: [generic pairing recursion](../../LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/ExpectationRecursion.lean), [scalar-exchange algebra](../../LeanCondensedMatter/Analysis/ScalarExchange.lean), [bosonic BDD peel](../../LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/BlochDeDominicis/OperatorPeel.lean), [completed fermionic BDD](../../LeanCondensedMatter/SecondQuantization/Fermionic/Thermal/Completed/BlochDeDominicis.lean), and [thermal architecture](../../notes/roadmaps/thermal-expectation-architecture.md).

Issue-focused chronology for this decision is maintained in [history-review.md](history-review.md).
