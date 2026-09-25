import LeanCondensedMatter.Analysis.Operator.Unbounded
import LeanCondensedMatter.Analysis.Operator.Spectral
import LeanCondensedMatter.Analysis.Operator.BerryGeometry
import LeanCondensedMatter.Analysis.Operator.FiniteTrace
import LeanCondensedMatter.Analysis.Operator.ZetaCommutator
import LeanCondensedMatter.Analysis.Operator.LinearCommutator
import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.Analysis.Operator.HilbertSchmidt
import LeanCondensedMatter.Analysis.Operator.Compact
import LeanCondensedMatter.Analysis.Operator.Diagonal
import LeanCondensedMatter.Analysis.Operator.Fredholm
import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import LeanCondensedMatter.Analysis.Operator.TraceClass

set_option linter.style.header false

/-!
# Operator analysis

Public routing module for the generic operator-analysis endpoints exported by
`LeanCondensedMatter.Analysis`, including the independent spectral and Berry-geometry routes.
Concrete realizations such as real-line `L²` multiplication,
one-dimensional Schwartz kinetic operators, and orbital-angular-momentum facts are intentionally
opt-in and remain available from their dedicated `Analysis.Operator` leaves.

Implementation modules should import the narrow operator leaves they actually use.
-/
