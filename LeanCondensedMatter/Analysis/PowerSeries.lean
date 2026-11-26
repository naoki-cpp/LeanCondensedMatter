import LeanCondensedMatter.Analysis.PowerSeries.AnalyticLog
import LeanCondensedMatter.Analysis.PowerSeries.CoefficientSum
import LeanCondensedMatter.Analysis.PowerSeries.Cumulant
import LeanCondensedMatter.Analysis.PowerSeries.FrobeniusWronskian
import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.Analysis.PowerSeries.Replica

set_option linter.style.header false

/-!
# Formal power series and analytic bridges

Public package boundary for the reusable formal power-series workflow used by
linked-cluster and thermal consumers. It exports constant-coefficient normalization,
factorial-normalized finite-set moments, formal-log derivative identities, and the finite-set cumulant
bridge, together with coefficientwise complex sums, their convergence-sensitive algebraic laws,
and formal Frobenius and Wronskian identities.
Specializing the generic moment–cumulant recurrence gives low-order logarithm formulas without
requiring separate order-specific theorems.

Coefficientwise complex sums keep explicit summability hypotheses for addition, subtraction, and
Cauchy multiplication. Constant multiplication and multiplication by X hold for the total sum;
the analytic logarithm bridge keeps its analytic power-series hypotheses. The remaining algebra is
purely formal. Normalization theorems require the original constant coefficient
to be nonzero, while logarithm/cumulant theorems on an already normalized series keep the explicit
constant-coefficient-one hypothesis.

The cumulant bridge depends only on the lower combinatorics leaves needed for finite-set inversion.
Pure set-partition modules that sit below that bridge continue to import the narrow Analysis leaf
when necessary rather than this package boundary, avoiding an umbrella-level import cycle.
-/
