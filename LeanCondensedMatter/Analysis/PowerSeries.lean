import LeanCondensedMatter.Analysis.PowerSeries.CoefficientSum
import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.Analysis.PowerSeries.Replica
import LeanCondensedMatter.Analysis.PowerSeries.ReplicaBridge
import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.Analysis.PowerSeries.AnalyticLog

set_option linter.style.header false

/-!
# Formal power series and analytic bridges

Public package boundary for the reusable formal power-series workflow used by
linked-cluster and thermal consumers. It exports constant-coefficient normalization,
factorial-normalized finite-set moments, formal-log derivative identities, and the finite-set cumulant
bridge, together with coefficientwise complex sums under explicit summability hypotheses.
Consumers who need order-specific logarithm formulas can import
`Analysis.PowerSeries.LowOrderLog`.

Coefficientwise complex evaluation keeps explicit summability hypotheses for its algebraic laws;
the analytic logarithm bridge keeps its analytic power-series hypotheses. The remaining algebra is
purely formal. Normalization theorems require the original constant coefficient
to be nonzero, while logarithm/cumulant theorems on an already normalized series keep the explicit
constant-coefficient-one hypothesis.

The cumulant bridge depends only on the lower combinatorics leaves needed for finite-set inversion.
Pure set-partition modules that sit below that bridge continue to import the narrow Analysis leaf
when necessary rather than this package boundary, avoiding an umbrella-level import cycle.
-/
