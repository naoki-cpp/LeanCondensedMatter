import LeanCondensedMatter.Analysis.InternalSpace
import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.Analysis.Dyson
import LeanCondensedMatter.Analysis.OrderedSimplex
import LeanCondensedMatter.Analysis.FunctionalCalculus
import LeanCondensedMatter.Analysis.Lorentzian
import LeanCondensedMatter.Analysis.Operator
import LeanCondensedMatter.Analysis.InfiniteSum
import LeanCondensedMatter.Analysis.Calculus
import LeanCondensedMatter.Analysis.Inequalities

set_option linter.style.header false

/-!
# Analysis

Public entry point for the analysis infrastructure exported by `LeanCondensedMatter`.

The public import surface is organized through package-level routing modules. This keeps the root
entry point aligned with the source hierarchy without widening the curated endpoint set. Implementation
modules should continue to import the narrow analysis leaves they actually use.
-/
