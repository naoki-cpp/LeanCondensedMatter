import LeanCondensedMatter.Analysis.Algebra.QuadraticNormalization
import LeanCondensedMatter.Analysis.Operator.AlgebraRestriction
import LeanCondensedMatter.Analysis.DiscreteLattice
import LeanCondensedMatter.Analysis.Fourier.FiniteCyclic
import LeanCondensedMatter.Analysis.SpecialFunctions.RegularizedHypergeometric
import LeanCondensedMatter.Analysis.LatticeGeometry
import LeanCondensedMatter.Analysis.Matrix.FinTwoCharpoly
import LeanCondensedMatter.Analysis.ScalarExchange
import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.Analysis.Dyson
import LeanCondensedMatter.Analysis.OrderedSimplex
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import LeanCondensedMatter.Analysis.Lorentzian
import LeanCondensedMatter.Analysis.Operator
import LeanCondensedMatter.Analysis.InfiniteSum.FinsuppProduct
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
