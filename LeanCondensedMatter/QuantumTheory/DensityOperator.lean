import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.QuantumTheory.DensityOperator.Pure
import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import LeanCondensedMatter.QuantumTheory.FiniteDimensional.DensityOperator
import LeanCondensedMatter.QuantumTheory.FiniteDimensional.Expectation
import LeanCondensedMatter.QuantumTheory.POVM.Basic
import LeanCondensedMatter.QuantumTheory.POVM.Born

/-!
# Canonical density-state API

This umbrella module exposes the dimension-independent density-operator, expectation, pure-state,
and discrete-POVM APIs. Finite-dimensional results are specializations of the same state type.
-/
