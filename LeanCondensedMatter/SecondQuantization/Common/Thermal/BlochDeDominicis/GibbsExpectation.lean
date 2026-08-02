import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Peel
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.FourPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Recursion

set_option linter.style.header false

/-!
# Umbrella module for normalized finite Gibbs expectations

Importing this module brings in the normalized finite Gibbs expectation, its two-/four-point and peel
identities, and its implementation of the generic `ExpectationPairingRecursion` contract.

`Common/Thermal/BlochDeDominicis/Induction.lean` imports the finite recursion implementation and then
applies the statistics-independent expectation recursion theorem.
-/
