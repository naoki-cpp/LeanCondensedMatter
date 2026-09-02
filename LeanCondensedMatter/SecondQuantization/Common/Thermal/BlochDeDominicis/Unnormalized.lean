import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelTermsIndexed

set_option linter.style.header false

/-!
# Unnormalized Bloch–de Dominicis recursion

Operator and trace identities that peel the first field from an ordered product before normalization
by a Gibbs partition function. The normalized expectation-value layer is kept separately under
`GibbsExpectation/`.
-/
