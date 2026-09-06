import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.SelfEnergy
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Denominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Boundary
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Damping
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.TransportRate
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagatorPolar
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderRegularity
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexRadialZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexRung
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexInfiniteCutoff

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent massive-Dirac transport benchmark. The continuum Born
chain is organized by physical and analytic responsibility: `Born.SelfEnergy` owns the finite-cutoff
self-energy and its polar provenance, `Born.Denominator` owns exact denominator evaluation and the
branch-oriented imaginary boundary analysis, `Born.Boundary` owns the finite metallic boundary value
as a complex number together with its scalar and `σ_z` propagation, `Born.Damping` projects that
complex API to the physical damping observables, `BornPropagator` feeds those damping channels into
the weak-disorder propagator and owns its retarded-advanced radial denominator pair, and
`TransportRate` owns the microscopic upper-band single-particle and transport scattering scales. The
finite-`η` Born-Dyson layer propagates the same fixed-cutoff boundary through its effective energy,
effective mass, and radial denominator before any weak-disorder or ultraviolet limit is taken.

The finite-external-broadening Born-Dyson propagator has a shared Cartesian-to-polar bridge before
its use in the current rung. The rung reduces through the shared polar Pauli algebra to an in-plane
coefficient pair `(X,Y)` with repository orientation `[[X,-Y],[Y,X]]`. Its fixed-radial-momentum
positive-broadening boundary is exposed separately, under the explicit nonzero boundary denominator
hypothesis needed by the inverse. Radial integration attaches the scalar-disorder line and physical
momentum measure exactly once. Passing `η → 0⁺` through that finite radial integral is exposed under
an explicit compact-radial uniform inverse bound for the RA denominator product; propagation through
the solved ladder remains a separate downstream step. `FiniteBroadeningLadderRegularity` owns the
shared determinant condition that licenses interpreting that algebraic coefficient pair as the
actual ladder fixed point. For the zero-external-broadening Born route, `BornCurrentVertexRung` owns
the exact normalized finite-cutoff longitudinal rung, while the fixed-cutoff weak-disorder and
infinite-cutoff limits remain separate downstream routes.

Physical charge-current conversion and Kubo/Středa insertion are downstream. SCBA/Ward closure,
crossed diagrams, and simultaneous thermodynamic, UV, disorder, and zero-broadening limits are not
asserted here.
-/
