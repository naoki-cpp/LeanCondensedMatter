import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization.Basic
import LeanCondensedMatter.Analysis.Operator.TraceClass.Factorization.Norm

set_option linter.style.header false

/-!
# Hilbert--Schmidt factorization of trace-class operators

The basic layer characterizes trace-class operators as products `A† B` of Hilbert--Schmidt
operators without depending on the trace-norm API. The norm layer adds trace-norm bounds and the
balanced factorization whose two squared Hilbert--Schmidt norms equal the trace norm.
-/
