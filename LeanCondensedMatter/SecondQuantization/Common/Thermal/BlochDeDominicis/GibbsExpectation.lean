import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Peel
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.FourPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Recursion

set_option linter.style.header false

/-!
# Normalized finite Gibbs pairing expectations

Pairing-specific two-point, four-point, and peel identities for the canonical finite Gibbs
expectation, together with its implementation of the generic `ExpectationPairingRecursion` contract.

The underlying finite Gibbs expectation and its trace/weighted-coordinate formulas are owned upstream
by `FiniteGibbsExpectationBridge.lean` and `FiniteGibbsCoordinate.lean`. This subtree only owns the
Bloch--de Dominicis specialization.
-/
