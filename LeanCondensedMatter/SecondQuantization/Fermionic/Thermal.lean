import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeEntropy
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.GrandCanonicalFreeGreenFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.OneBodyExpectation
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.BoltzmannSummability
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed

set_option linter.style.header false

/-!
# Fermionic free thermal theory

Finite-basis and completed-Hilbert free-fermion thermal theory, including generic pure-point
Gibbs expectations, the shared explicit-μ grand-canonical partition function and its finite-mode
product formula, Fermi--Dirac observables, entropy, and Green functions and contractions. Completed
thermal theory includes grand-canonical number expectation, ladder/KMS/pairing, and finite-mode
Gibbs convergence. The separate finite density-state API still has implicit μ = 0 pending migration.

Completed thermal modules depend on the representation and operator infrastructure in
`Fermionic.CompletedSpace`; the representation umbrella does not own the thermal stack.
-/
