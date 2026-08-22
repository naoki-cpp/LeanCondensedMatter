import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeConnectedCycleSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeEntropy
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsGreenFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.QuantumLinkedCluster
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.BlochDeDominicis.Examples.SingleMode
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.FreeGibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.GibbsLadderIntertwining
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalLadder
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalPeel
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalPeelIndexed
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalKMS
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalFirstPair
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalRecursion

set_option linter.style.header false

/-!
# Fermionic free thermal theory

Canonical public entry point for finite-basis and completed-Hilbert free-fermion thermal theory.
It exposes weighted and Gibbs expectations, partition functions, Fermi--Dirac observables, entropy,
Green functions and contractions, concrete Bloch--de Dominicis specializations, and the completed
free-Gibbs ladder/KMS/pairing-recursion stack.

Completed thermal modules depend on the representation and operator infrastructure in
`Fermionic.CompletedSpace`; the representation umbrella does not own the thermal stack.
-/
