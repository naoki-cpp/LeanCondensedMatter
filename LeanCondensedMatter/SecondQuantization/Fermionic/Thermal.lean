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

set_option linter.style.header false

/-!
# Fermionic free thermal theory

Finite-basis weighted and Gibbs expectations, the free partition function, Fermi–Dirac occupation
numbers and entropy, closed-form free Gibbs Green functions and contractions, concrete
Bloch–de Dominicis specializations, and the completed-Hilbert free Gibbs specialization.
-/
