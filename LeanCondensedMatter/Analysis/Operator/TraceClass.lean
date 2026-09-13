import LeanCondensedMatter.Analysis.Operator.TraceClass.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import LeanCondensedMatter.Analysis.Operator.TraceClass.Diagonal
import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalPositive
import LeanCondensedMatter.Analysis.Operator.TraceClass.DiagonalSpectralTrace
import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops
import LeanCondensedMatter.Analysis.Operator.TraceClass.Equality
import LeanCondensedMatter.Analysis.Operator.TraceClass.Scalar

set_option linter.style.header false

/-!
# Trace-class operators

Public routing module for the trace-class endpoints exported by `LeanCondensedMatter.Analysis`.
The additional `TraceClass.Unitary` development remains directly importable but is not added to the
root public surface by this refactor.
-/
