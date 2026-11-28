import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.ExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.NormalizedTwoPointTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation

set_option linter.style.header false

/-!
# Bloch–de Dominicis theorem

Statistics-weighted pairing sums, abstract first-pair expectation recursion, summable trace
peeling, normalized two-point identities, and finite Gibbs pairing theorems.
The abstract recursion does not require finite configuration spaces; admissibility expresses
the domain and summability requirements of concrete realizations.
-/
