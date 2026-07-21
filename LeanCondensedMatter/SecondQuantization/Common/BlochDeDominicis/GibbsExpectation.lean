import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.Peel
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.GibbsExpectation.FourPoint

set_option linter.style.header false

/-!
# Umbrella module for the normalized Gibbs expectation

Importing this module brings in the whole `GibbsExpectation/` subdirectory: the normalized
functional itself and its basic algebraic properties (`Core.lean`), the genuine normalized
2-point value (`TwoPoint.lean`), the normalized peel identities (`Peel.lean`), and the normalized
4-point identities (`FourPoint.lean`). `Common/BlochDeDominicis/Induction.lean` — which needs only
`Core`/`TwoPoint`/`Peel`, not `FourPoint` — imports those three directly instead of this umbrella.
-/
