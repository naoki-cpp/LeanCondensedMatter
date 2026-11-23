import LeanCondensedMatter.Analysis.Operator.TraceClass.General
import LeanCondensedMatter.Analysis.Operator.TraceClass.Diagonal
import LeanCondensedMatter.Analysis.Operator.TraceClass.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.Trace
import LeanCondensedMatter.Analysis.Operator.TraceClass.Positive
import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Ops.Norm
import LeanCondensedMatter.Analysis.Operator.TraceClass.AdjointConjugation
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Bundled
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Diagonal
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Ops
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Equality

set_option linter.style.header false

/-!
# Trace-class operators

General trace-class membership, compactness, trace norm, and complex trace together with the
self-adjoint spectral specialization.
-/
