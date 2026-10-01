import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Bundled
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Diagonal
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Ops
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Equality
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Scalar
import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Unitary

set_option linter.style.header false

/-!
# Spectral trace class

Compact self-adjoint spectral trace infrastructure, kept separate from the general non-self-adjoint
trace-class membership layer.
-/
