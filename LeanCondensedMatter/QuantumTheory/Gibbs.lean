import LeanCondensedMatter.QuantumTheory.Gibbs.State
import LeanCondensedMatter.QuantumTheory.Gibbs.Boltzmann
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis
import LeanCondensedMatter.QuantumTheory.Gibbs.HeatOperator
import LeanCondensedMatter.QuantumTheory.Gibbs.EigenbasisExpectation
import LeanCondensedMatter.QuantumTheory.Gibbs.EigenbasisEntropy
import LeanCondensedMatter.QuantumTheory.Gibbs.DistributionVariational
import LeanCondensedMatter.QuantumTheory.Gibbs.DistributionUniqueness
import LeanCondensedMatter.QuantumTheory.Gibbs.EnergyExpectation
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy
import LeanCondensedMatter.QuantumTheory.Gibbs.DiagonalEnergy
import LeanCondensedMatter.QuantumTheory.Gibbs.FreeBoltzmannKernel
import LeanCondensedMatter.QuantumTheory.Gibbs.Variational
import LeanCondensedMatter.QuantumTheory.Gibbs.EqualityComponents
import LeanCondensedMatter.QuantumTheory.Gibbs.MinimizerUniqueness

set_option linter.style.header false

/-!
# Gibbs-state theory

Gibbs states and equilibrium thermodynamics: heat operators, pure-point expectations and entropy,
energy expectation, free energy, diagonal-energy formulas, one-particle Boltzmann kernels,
variational principles, and uniqueness results.
-/
