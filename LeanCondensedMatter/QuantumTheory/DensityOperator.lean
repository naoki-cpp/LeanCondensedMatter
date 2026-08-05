import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.QuantumTheory.DensityOperator.Pure
import LeanCondensedMatter.QuantumTheory.DensityOperator.Purity
import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation
import LeanCondensedMatter.QuantumTheory.FiniteDimensional.DensityOperator
import LeanCondensedMatter.QuantumTheory.FiniteDimensional.Expectation
import LeanCondensedMatter.QuantumTheory.FiniteDimensional.Purity
import LeanCondensedMatter.QuantumTheory.POVM.Basic
import LeanCondensedMatter.QuantumTheory.POVM.Born

/-!
# Canonical density-state API

This umbrella module exposes the dimension-independent density-operator, pure-state, purity,
complex expectation, real observable-expectation, and discrete-POVM APIs. Finite-dimensional results
are specializations of the same state type.
-/
