import LeanCondensedMatter.QuantumTheory.Gibbs.State
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint
import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointExpectation
import LeanCondensedMatter.QuantumTheory.Gibbs.EnergyExpectation
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy
import LeanCondensedMatter.QuantumTheory.Gibbs.Entropy
import LeanCondensedMatter.QuantumTheory.Gibbs.DiagonalEnergy
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeBoltzmannKernel
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeExchangeCycleSeries
import LeanCondensedMatter.QuantumTheory.Gibbs.Variational
import LeanCondensedMatter.QuantumTheory.Gibbs.Equality
import LeanCondensedMatter.QuantumTheory.Gibbs.Uniqueness
import LeanCondensedMatter.QuantumTheory.Gibbs.MinimizerUniqueness

set_option linter.style.header false

/-!
# Gibbs-state theory

Public routing module for Gibbs states, heat-operator compatibility, free energy, one-particle
Boltzmann kernels, thermal exchange-cycle series, variational principles, and uniqueness
infrastructure exported by
`LeanCondensedMatter.QuantumTheory`.
-/
