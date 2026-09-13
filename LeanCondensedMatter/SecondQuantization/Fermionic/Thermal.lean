import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeConnectedCycleSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeEntropy
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsGreenFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.OccupationCumulant
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsSummability
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.UnboundedExpectation
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed

set_option linter.style.header false

/-!
# Fermionic free thermal theory

Canonical public entry point for finite-basis and completed-Hilbert free-fermion thermal theory.
It exposes weighted and Gibbs expectations, occupation moments and cumulants, including integrable
unbounded diagonal expectations, partition functions, Fermi--Dirac observables, entropy, Green
functions and contractions, concrete Bloch--de Dominicis specializations, mode-level Gibbs
summability, and completed free-Gibbs ladder/KMS/pairing plus finite-mode Gibbs convergence.

Completed thermal modules depend on the representation and operator infrastructure in
`Fermionic.CompletedSpace`; the representation umbrella does not own the thermal stack.
-/
