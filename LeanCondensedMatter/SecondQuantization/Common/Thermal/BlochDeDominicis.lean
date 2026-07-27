import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Bloch–de Dominicis theorem

The shared finite-temperature pairing theory is organized into three layers:

- `Unnormalized`: operator/trace peel identities before division by the partition function;
- `GibbsExpectation`: normalized Gibbs functionals and their two-point and four-point recursion lemmas;
- `Induction`: the arbitrary-length pairing theorem.

`PairingWeight` supplies the statistics-dependent crossing factor used by the final expansion.
-/
