import LeanCondensedMatter.Analysis.OscillatoryIntegral
import LeanCondensedMatter.Analysis.Algebra
import LeanCondensedMatter.Analysis.DiscreteLattice
import LeanCondensedMatter.Analysis.Fourier
import LeanCondensedMatter.Analysis.Geometry.SphericalMoments
import LeanCondensedMatter.Analysis.Matrix
import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.Analysis.ODE.RadialEnergyDecay
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel
import LeanCondensedMatter.Analysis.Dyson
import LeanCondensedMatter.Analysis.OrderedSimplex
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import LeanCondensedMatter.Analysis.Lorentzian
import LeanCondensedMatter.Analysis.Operator
import LeanCondensedMatter.Analysis.InfiniteSum
import LeanCondensedMatter.Analysis.Calculus
import LeanCondensedMatter.Analysis.ConservationLaw
import LeanCondensedMatter.Analysis.Inequalities

set_option linter.style.header false

/-!
# Analysis

General mathematical infrastructure used throughout LeanCondensedMatter: scalar-exchange algebra,
formal power series, Dyson and ordered-simplex analysis, Lorentzian identities, operator theory,
infinite sums, calculus, abstract conservation laws, and analytic inequalities.

The one-dimensional weak-conservation kernel is opt-in: import
`LeanCondensedMatter.Analysis.ConservationLaw.WeakConservation1D` when needed.
-/
