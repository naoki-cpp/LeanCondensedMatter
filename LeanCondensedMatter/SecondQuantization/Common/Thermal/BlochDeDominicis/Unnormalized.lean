import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace

set_option linter.style.header false

/-!
# Unnormalized Bloch–de Dominicis recursion

A configuration-general trace identity obtained from scalar exchange and KMS rotation before
normalization by a Gibbs partition function. The underlying product algebra is owned by
`Analysis.ScalarExchange.Peel`; normalized expectations live separately under `GibbsExpectation/`.
-/
