import LeanCondensedMatter.Models.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Models.MassiveDirac.Disorder.ScalarAngularWeights
import LeanCondensedMatter.Models.MassiveDirac.Disorder.SingleParticleRate
import LeanCondensedMatter.Models.MassiveDirac.Disorder.TransportRate
import LeanCondensedMatter.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.UltravioletSelfEnergy
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.DysonShift
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RadialMoments
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.RadialGreen
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.ScalarGenerator
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.ScalarTail
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVFinitePart
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.FrozenCutoffUV
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVBesselJ
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVUnitVelocity
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVHankelReduction
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVHankelUnitReduction
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.RadialUVResolventDifference
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.ScalarGrid
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.Green
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.BornDyson.DressedCurrent
import LeanCondensedMatter.Models.MassiveDirac.Disorder.TMatrix
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Ladder.RegulatorBoundaryWeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Ladder.RegulatorBoundaryTransverseWeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Born.WeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Born.InfiniteCutoff

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Disorder-dependent transport for the massive-Dirac benchmark. The continuum Born
chain is organized by physical and analytic responsibility: `ContinuumMeasurePrefactor` owns one
scalar-disorder line together with exactly one physical-momentum-measure factor, independently of
where a consumer performs angular reduction; `Born.SelfEnergy` owns the finite-cutoff self-energy and
its polar provenance; `Born.Denominator` owns exact denominator evaluation and the branch-oriented
imaginary boundary analysis; `Born.Boundary` owns the finite metallic boundary value as a complex
number together with its scalar and `σ_z` propagation; `Born.Damping` projects that complex API to
the physical damping observables; `Disorder.Propagator.Born.WeakDisorder` feeds those damping channels into the
weak-disorder propagator and owns its retarded-advanced radial denominator pair;
`ScalarAngularWeights` owns the angular overlap and current-relaxation integrals;
`SingleParticleRate` owns the Born single-particle rate and lifetime; and `TransportRate` owns
the corresponding transport scattering rate and lifetime. The finite-`η`
Born-Dyson layer propagates the same fixed-cutoff boundary through its effective energy, effective
mass, and radial denominator before any weak-disorder or ultraviolet limit is taken.
`Disorder.Propagator.BornDyson.RadialMoments` owns the single-pole logarithmic integral,
arbitrary-weight RA double-pole spectral difference, and its logarithmic specialization.
These analytic identities are independent of the longitudinal same-side Středa
remainder and are consumed by Gaussian-crossed harmonics.
`Disorder.Propagator.BornDyson.RegulatorBoundary` owns that propagator boundary together with the real Born
renormalization and the denominator nonvanishing guarantee protected by the renormalization bound.

`Disorder.Propagator.BornDyson.Green` owns the finite-broadening Dyson Green and its
Cartesian-to-polar representation; `Disorder.Propagator.BornDyson.DysonShift` proves inverse and adjoint
identities for the Dyson shift, consumed by the dissipative invertibility analysis. `Disorder.Propagator.BornDyson.RealSpace.RadialGreen` owns the one-dimensional radial Green kernels,
integrals, and signed-radius inversion; `Disorder.Propagator.BornDyson.RealSpace.Green` owns the
full-angle Fourier representation and its exact radial-axis identification, using the generic
physical-momentum polar Fourier transform from `Transport.Analysis`. `Disorder.Vertex.BornDyson.CurrentVertex` owns the direction-indexed
in-plane rung, its common RA denominator form, radial normalization, solved coefficient pair, and the
determinant condition that licenses interpreting that pair as the actual ladder fixed point.
`Disorder.Vertex.BornDyson.DressedCurrent` owns the source-indexed dressed current insertion and the
reduced longitudinal factor consumed by response modules, while keeping ladder regularity as a
separate interpretation condition. Its
fixed-radial-momentum positive-broadening boundary is exposed separately, under the explicit nonzero
boundary denominator hypothesis needed by the inverse. The zero-broadening integral bridge uses
dominated convergence and consumes propagator regularity from the common Born-Dyson boundary. At
fixed positive disorder, an explicit real-renormalization bound below one makes the boundary RA
denominator nonzero and discharges the compact radial regularity needed for the integrated limit. The
resulting integrated-rung boundary is propagated through the canonical two-component ladder under an
explicit nonzero boundary determinant. The subsequent fixed-cutoff weak-disorder limit is taken only
after this zero-broadening boundary is formed, retaining both the finite longitudinal rung and the
first nonvanishing disorder-scaled transverse coefficient needed by ordered Hall response. For the
zero-external-broadening Born route, `BornCurrentVertexRung` owns the exact normalized finite-cutoff
longitudinal rung while consuming the same shared disorder/measure factor; its fixed-cutoff
weak-disorder and infinite-cutoff limits remain separate downstream routes.

Physical charge-current conversion and Kubo/Středa insertion are downstream. SCBA/Ward closure,
crossed diagrams, and simultaneous thermodynamic, UV, disorder, and zero-broadening limits are not
asserted here.
-/
