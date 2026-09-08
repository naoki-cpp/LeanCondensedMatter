import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningLadderZeroBroadening
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

`FiniteBroadeningBornPropagator` also owns the Cartesian-to-polar representation used by the finite-
external-broadening current rung. `FiniteBroadeningCurrentVertex` owns the direction-indexed in-plane
rung, its common RA denominator form, radial normalization, solved coefficient pair, and the
determinant condition that licenses interpreting that pair as the actual ladder fixed point. Its
fixed-radial-momentum positive-broadening boundary is exposed separately, under the explicit nonzero
boundary denominator hypothesis needed by the inverse. The zero-broadening integral bridge uses
dominated convergence. At fixed positive disorder, an explicit real-renormalization bound below one
makes the boundary RA denominator nonzero and discharges the compact radial regularity needed for the
integrated limit. The resulting integrated-rung boundary is then propagated through the canonical
two-component ladder under an explicit nonzero boundary determinant. For the zero-external-
broadening Born route, `BornCurrentVertexRung` owns the exact normalized finite-cutoff longitudinal
rung, while the fixed-cutoff weak-disorder and infinite-cutoff limits remain separate downstream
routes.

Physical charge-current conversion and Kubo/Středa insertion are downstream. SCBA/Ward closure,
crossed diagrams, and simultaneous thermodynamic, UV, disorder, and zero-broadening limits are not
asserted here.
-/
