import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.Analysis.PowerSeries.LogAlgebra
import LeanCondensedMatter.Analysis.PowerSeries.Replica
import LeanCondensedMatter.Analysis.PowerSeries.ReplicaBridge
import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.Analysis.PowerSeries.LowOrderLog

set_option linter.style.header false

/-!
# Normalized formal power series

Public package boundary for the reusable formal power-series workflow used by linked-cluster and
thermal consumers. It exports constant-coefficient normalization, formal-log algebra, the
finite-set cumulant bridge, and low-order logarithm formulas.

All results remain purely formal. Normalization theorems require the original constant coefficient
to be nonzero, while logarithm/cumulant theorems on an already normalized series keep the explicit
constant-coefficient-one hypothesis.

The cumulant bridge depends only on the lower combinatorics leaves needed for finite-set inversion.
Pure set-partition modules that sit below that bridge continue to import the narrow Analysis leaf
when necessary rather than this package boundary, avoiding an umbrella-level import cycle.
-/
