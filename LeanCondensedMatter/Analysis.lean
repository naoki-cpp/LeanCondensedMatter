import LeanCondensedMatter.Analysis.OscillatoryIntegral
import LeanCondensedMatter.Analysis.Algebra
import LeanCondensedMatter.Analysis.DiscreteLattice
import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import LeanCondensedMatter.Analysis.Geometry.SphericalMoments
import LeanCondensedMatter.Analysis.Fourier.FiniteCyclic
import LeanCondensedMatter.Analysis.Matrix.CartesianProjectors
import LeanCondensedMatter.Analysis.Matrix.FinTwoCharpoly
import LeanCondensedMatter.Analysis.ScalarExchange.Basic
import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.Analysis.PowerSeries.FrobeniusWronskian
import LeanCondensedMatter.Analysis.ODE.RadialEnergyDecay
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.RadialMoments
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.AnalyticWronskian
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.YSeries
import LeanCondensedMatter.Analysis.Dyson
import LeanCondensedMatter.Analysis.OrderedSimplex
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import LeanCondensedMatter.Analysis.Lorentzian
import LeanCondensedMatter.Analysis.Operator
import LeanCondensedMatter.Analysis.InfiniteSum.FinsuppProduct
import LeanCondensedMatter.Analysis.Calculus.AlgebraicDerivative
import LeanCondensedMatter.Analysis.Calculus.CompactSupportInterval
import LeanCondensedMatter.Analysis.ConservationLaw
import LeanCondensedMatter.Analysis.Inequalities.PeierlsBogoliubov

set_option linter.style.header false

/-!
# Analysis

General mathematical infrastructure used throughout LeanCondensedMatter: scalar-exchange algebra,
formal power series, Dyson and ordered-simplex analysis, Lorentzian identities, operator theory,
infinite sums, calculus, abstract conservation laws, and analytic inequalities.

The one-dimensional weak-conservation kernel is opt-in: import
`LeanCondensedMatter.Analysis.ConservationLaw.WeakConservation1D` when needed.
-/
