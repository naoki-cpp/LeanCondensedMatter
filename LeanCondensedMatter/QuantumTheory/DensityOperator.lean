import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.QuantumTheory.DensityOperator.Normalize
import LeanCondensedMatter.QuantumTheory.DensityOperator.Pure
import LeanCondensedMatter.QuantumTheory.DensityOperator.PureState
import LeanCondensedMatter.QuantumTheory.DensityOperator.Purity
import LeanCondensedMatter.QuantumTheory.DensityOperator.Expectation
import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.DensityOperator.Finite
import LeanCondensedMatter.QuantumTheory.POVM

/-!
# Canonical density-state API

This umbrella module exposes the dimension-independent density-operator, physical pure-state,
purity, positive trace-class normalization, complex expectation, real observable-expectation,
countable diagonal-expectation, and discrete-POVM APIs. The POVM re-export is retained for
existing importers; new measurement-specific clients can use `QuantumTheory.POVM` directly.
Finite-dimensional results are specializations of the same density-state type.
-/
