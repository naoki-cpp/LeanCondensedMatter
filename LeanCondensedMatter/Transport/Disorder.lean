import LeanCondensedMatter.Transport.Disorder.ConnectedCorrelation
import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.Transport.Disorder.Resolvent
import LeanCondensedMatter.Transport.Disorder.TwoParticle
import LeanCondensedMatter.Transport.Disorder.TwoParticleNormBound
import LeanCondensedMatter.Transport.Disorder.LinearizedFluctuation
import LeanCondensedMatter.Transport.Disorder.FirstRungNormBound
import LeanCondensedMatter.Transport.Disorder.LadderNormBound
import LeanCondensedMatter.Transport.Disorder.ConnectedLadderNormBound
import LeanCondensedMatter.Transport.Disorder.TraceBridge
import LeanCondensedMatter.Transport.Disorder.TraceNormBound
import LeanCondensedMatter.Transport.Disorder.DressedTraceNormBound
import LeanCondensedMatter.Transport.Disorder.AveragedSelfEnergy
import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Born
import LeanCondensedMatter.Transport.Disorder.BornNormBound
import LeanCondensedMatter.Transport.Disorder.Ladder
import LeanCondensedMatter.Transport.Disorder.SCBA
import LeanCondensedMatter.Transport.Disorder.Ward

set_option linter.style.header false

/-!
# Finite disorder transport

Finite disorder ensembles and their transport algebra: connected correlations, exact two-Green
insertions, fixed-regulator covariance and controlled first-rung and norm-convergent resummed-ladder bounds, and their finite-dimensional Středa trace bridge and quantitative exact-vs-dressed trace bounds,
disorder covariance and moments,
disorder resolvents and averaged Green functions
and self-energy, first-Born self-energy and fixed-regulator cubic-remainder estimates,
retarded–advanced covariance ladders,
self-consistent Born approximation, and the finite bounded charge-vertex Ward identity.
-/
