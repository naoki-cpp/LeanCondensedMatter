import LeanCondensedMatter.Analysis.Algebra
import LeanCondensedMatter.Analysis.Calculus
import LeanCondensedMatter.Analysis.ConservationLaw
import LeanCondensedMatter.Analysis.DiscreteLattice
import LeanCondensedMatter.Analysis.Dyson
import LeanCondensedMatter.Analysis.Fourier
import LeanCondensedMatter.Analysis.FunctionalCalculus
import LeanCondensedMatter.Analysis.Geometry
import LeanCondensedMatter.Analysis.Inequalities
import LeanCondensedMatter.Analysis.InfiniteSum
import LeanCondensedMatter.Analysis.InternalSpace
import LeanCondensedMatter.Analysis.Lorentzian
import LeanCondensedMatter.Analysis.Matrix
import LeanCondensedMatter.Analysis.ODE
import LeanCondensedMatter.Analysis.Operator
import LeanCondensedMatter.Analysis.OrderedSimplex
import LeanCondensedMatter.Analysis.OscillatoryIntegral
import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.Analysis.ScalarExchange
import LeanCondensedMatter.Analysis.SpecialFunctions

set_option linter.style.header false

/-!
# Analysis

Public entry point for the general mathematical infrastructure used throughout LeanCondensedMatter.
Each immediate subdirectory is represented by its topic umbrella; standalone modules at this level
are imported directly. Consumers should import the narrow canonical module they need.

The one-dimensional weak-conservation kernel is opt-in: import
`LeanCondensedMatter.Analysis.ConservationLaw.WeakConservation1D` when needed.
-/
