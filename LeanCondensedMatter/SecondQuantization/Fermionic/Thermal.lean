import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedFreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeEntropy
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeTwoPointFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.WeightedContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.QuantumLinkedCluster
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.BlochDeDominicis.Examples.SingleMode
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.BlochDeDominicis.TwoPoint

set_option linter.style.header false

/-!
# Fermionic free thermal theory

Finite-basis weighted and Gibbs expectations, the free partition function, Fermi–Dirac occupation
numbers and entropy, free two-point functions and contractions, and concrete Bloch–de Dominicis
specializations.
-/
