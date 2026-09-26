import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.TimedFieldContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeConnectedCycleSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeEntropy
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsGreenFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.PurePointSummability
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed

set_option linter.style.header false

/-!
# Fermionic free thermal theory

Finite-basis and completed-Hilbert free-fermion thermal theory, including canonical Gibbs
expectations, partition functions, Fermi--Dirac observables, entropy,
Green functions and contractions, pure-point Gibbs summability, and completed free-Gibbs
total-number expectation, ladder/KMS/pairing, and finite-mode Gibbs convergence.

Completed thermal modules depend on the representation and operator infrastructure in
`Fermionic.CompletedSpace`; the representation umbrella does not own the thermal stack.
-/
