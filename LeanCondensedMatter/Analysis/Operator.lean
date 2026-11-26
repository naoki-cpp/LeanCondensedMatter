import LeanCondensedMatter.Analysis.Operator.AdjointConjugation
import LeanCondensedMatter.Analysis.Operator.AlgebraRestriction
import LeanCondensedMatter.Analysis.Operator.BerryGeometry
import LeanCondensedMatter.Analysis.Operator.Compact
import LeanCondensedMatter.Analysis.Operator.Diagonal
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import LeanCondensedMatter.Analysis.Operator.Exponential
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import LeanCondensedMatter.Analysis.Operator.Fredholm
import LeanCondensedMatter.Analysis.Operator.HilbertBasis
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt
import LeanCondensedMatter.Analysis.Operator.L2Multiplication
import LeanCondensedMatter.Analysis.Operator.Polar
import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
import LeanCondensedMatter.Analysis.Operator.SchwartzTwoLevel1D
import LeanCondensedMatter.Analysis.Operator.Spectral
import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.Analysis.Operator.TraceClass
import LeanCondensedMatter.Analysis.Operator.Unbounded
import LeanCondensedMatter.Analysis.Operator.Unitary

set_option linter.style.header false

/-!
# Operator analysis

General operator-theoretic infrastructure used across the project: unbounded self-adjoint evolution,
spectral and resolvent theory, Berry geometry, finite traces, commutators and symmetrized products,
Hilbert–Schmidt, compact, diagonal, Fredholm, expectation, trace-class, algebra restriction,
bounded multiplication on L², and scalar and two-component Schwartz operator algebra.

Concrete physical realizations of these abstractions live in the corresponding quantum-mechanical
or transport layers.
-/
