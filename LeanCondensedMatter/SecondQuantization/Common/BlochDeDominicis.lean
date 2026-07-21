import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.FourPointReduction
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirst
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelTermsIndexed
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.Induction

set_option linter.style.header false

/-!
# Umbrella module for the finite-temperature Bloch–de Dominicis theorem

Importing this module brings in the whole `BlochDeDominicis/` subdirectory: the pairing weight
(`PairingWeight.lean`), the un-normalized 2-point/4-point/arbitrary-length peel identities
(`TwoPoint.lean`/`FourPointReduction.lean`/`PeelFirst.lean`/`PeelFirstTrace.lean`/
`PeelTermsIndexed.lean`), the normalized Gibbs expectation built on top of them
(`GibbsExpectation.lean`), and the general `n`-point theorem itself (`Induction.lean`).

Keeps `SecondQuantization/Common.lean` from having to enumerate this subdirectory's own internal
structure (including the purely-combinatorial `Combinatorics/` files each piece depends on).
-/
