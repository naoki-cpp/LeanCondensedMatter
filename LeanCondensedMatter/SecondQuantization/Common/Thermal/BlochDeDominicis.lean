import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Bloch–de Dominicis theorem

The shared finite-temperature pairing theory is organized into four layers:

- `PairingWeight`: the statistics-dependent crossing factor;
- `ExpectationRecursion`: the basis- and implementation-independent normalized expectation/KMS
  contract and its pairing theorem;
- `Unnormalized` and `GibbsExpectation`: concrete operator, trace, and finite Gibbs identities that
  discharge the contract;
- `Induction`: the public finite Gibbs specialization of the generic pairing theorem.
-/
