import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.NormalizedTwoPointTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation

set_option linter.style.header false

/-!
# Bloch–de Dominicis theorem

The shared finite-temperature pairing theory is organized into reusable layers:

- `PairingWeight`: the statistics-dependent crossing factor;
- `ExpectationRecursion`: the basis-, representation-, and implementation-independent normalized
  expectation/KMS contract and its pairing theorem;
- `Unnormalized/PeelFirstTrace`: configuration-general operator and summable trace peel identities;
- `NormalizedTwoPointTrace`: a configuration-general normalized two-point trace-ratio identity;
- `GibbsExpectation`: finite Gibbs density-state identities that discharge the recursion contract,
  including the public finite-configuration Gibbs pairing theorem.

The generic recursion has no configuration type or `Fintype` assumption. Its `admissible` predicate
is the extension point for summability, integrability, product-closure, or domain hypotheses in a
bosonic implementation. Finite occupation-basis formulas live outside this hierarchy behind an
explicit bridge and are not the normalized-state abstraction.
-/
