import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.OperatorPeel
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Bloch–de Dominicis theorem

The shared finite-temperature pairing theory is organized into reusable layers:

- `PairingWeight`: the statistics-dependent crossing factor;
- `ExpectationRecursion`: the basis-, representation-, and implementation-independent normalized
  expectation/KMS contract and its pairing theorem;
- `OperatorPeel`: the representation-independent finite operator-exchange identity preceding KMS
  rotation;
- `Unnormalized` and `GibbsExpectation`: concrete operator, trace-ratio, and finite Gibbs identities
  that discharge the contract;
- `Induction`: the public finite Gibbs specialization of the generic pairing theorem.

The generic recursion has no configuration type or `Fintype` assumption. Its `admissible` predicate
is the extension point for summability, integrability, product-closure, or domain hypotheses in a
bosonic implementation. Finite occupation-basis formulas live outside this hierarchy behind an
explicit bridge and are not the normalized-state abstraction.
-/
