import LeanCondensedMatter.QuantumTheory.Gibbs.State
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint
import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointExpectation
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointEntropy
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointVariational
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointUniqueness
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

Gibbs states and equilibrium thermodynamics: heat operators, pure-point expectations and entropy,
energy expectation, free energy, diagonal-energy formulas, one-particle Boltzmann kernels,
exchange-cycle series, variational principles, and uniqueness results.
-/
