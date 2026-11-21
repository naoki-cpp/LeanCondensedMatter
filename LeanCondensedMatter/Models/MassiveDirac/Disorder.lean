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
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.FinitePart
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.FrozenCutoffUV
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.FrozenCutoffBesselJ
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.HankelScaling
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.HankelReduction
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.ResolventDifference
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
# Massive-Dirac scalar-disorder transport

Umbrella import for scalar disorder in the two-dimensional massive-Dirac model. It collects
finite-ensemble covariance, continuum Born scattering, finite-regulator Born-Dyson Green
functions and current vertices, scalar-impurity T-matrices, and the radial Fourier tools
needed for their real-space representations. Definitions and proofs belong to the imported
modules; this file introduces no additional approximation or limit theorem.

## Disorder input and scattering times

* `Disorder.ScalarCovariance` proves the exact second-moment identity for an explicitly
  supplied finite ensemble of scalar potentials. It does not assume continuum white noise
  or identify a Born Green function with an exact disorder average.
* `Disorder.ContinuumMeasurePrefactor` combines one continuum scalar-disorder line
  with one physical two-dimensional momentum-measure factor. Angular reduction and
  conductivity normalization are separate operations.
* `Disorder.ScalarAngularWeights` evaluates upper-band overlap and
  `1 - cos θ` current-relaxation weights. `Disorder.SingleParticleRate` derives the
  Born single-particle rate from damping, whereas `Disorder.TransportRate` supplies
  the distinct transport rate and lifetime.

## Continuum Born and Born-Dyson propagators

* `Disorder.Born.SelfEnergy` packages finite-cutoff radial self-energy integrals and
  their polar normalization; `Born.Denominator` evaluates the common integral,
  `Born.Boundary` gives its fixed-cutoff complex `η → 0⁺` boundary, and
  `Born.Damping` extracts the physical upper-band width. These modules are reached
  through the imports below. `Born.UltravioletSelfEnergy` records the separate
  logarithmic UV behavior of the unrenormalized self-energy.
* `Disorder.Propagator.BornDyson.Green` constructs the finite-broadening,
  finite-cutoff Green function from the Born self-energy, not from a self-consistent
  closure. `BornDyson.DysonShift` and `BornDyson.Invertibility` establish its
  inverse and nonvanishing-denominator properties; `BornDyson.RadialMoments`
  supplies regulated radial resolvent identities.
* `BornDyson.RegulatorBoundary` takes the external-broadening boundary at fixed
  disorder strength and cutoff, subject to its stated regularity hypotheses.
  This boundary is distinct from the subsequent weak-disorder limit.

## Real-space Green functions and radial Fourier analysis

* `BornDyson.RealSpace.RadialGreen` defines the radial Green integrals;
  `ScalarGenerator` and `ScalarTail` reduce their components to a scalar Fourier
  generator and a tail identity. `RealSpace.Green` supplies the full two-dimensional
  Fourier representation, and `ScalarGrid` gives a finite radial discretization
  without a convergence claim.
* `RealSpace.FrozenCutoffUV` and `FrozenCutoffBesselJ` remove an **outer Fourier**
  cutoff while the **Born self-energy cutoff remains fixed**. They do not take
  an unrenormalized diagonal cutoff limit with running Born parameters.
* `MassiveDirac.Propagator.RadialFourier.FinitePart`, `ResolventDifference`,
  `HankelReduction`, and `HankelScaling` are fixed-spectral-center Fourier
  analysis, not new disorder approximations. In particular, `HankelReduction`
  reduces the proposed outgoing Hankel evaluation to a further transform
  identity; it does not prove that identity unconditionally.

## Current vertices and T-matrices

* `Disorder.Vertex.BornDyson.CurrentVertex` reduces the finite-regulator
  retarded-advanced rung to the two-component in-plane ladder;
  `BornDyson.DressedCurrent` exposes its current-operator insertion. The algebraic
  solution represents a ladder fixed point only under the required nonzero
  determinant hypothesis.
* `Vertex.Ladder.RegulatorBoundary` first propagates the fixed-disorder
  zero-broadening boundary. `RegulatorBoundaryWeakDisorder` then takes the
  fixed-cutoff weak-disorder limit, while
  `RegulatorBoundaryTransverseWeakDisorder` retains the first nonzero
  disorder-scaled transverse term for ordered Hall response.
* The separate `Vertex.Born.Rung` route has a normalized finite-cutoff
  retarded-advanced current rung; `Born.WeakDisorder` and
  `Born.InfiniteCutoff` study different, explicitly ordered limits.
  Neither route supplies a Kubo conductivity theorem by itself.
* `Disorder.TMatrix` exports the supplied-loop scalar-impurity T-matrix
  algebra and its finite-cutoff Born-Dyson loop specialization. The
  small-impurity-strength Born identification is not an SCBA or
  self-consistent T-matrix equation.

Physical current conversion, Kubo/Středa traces, conductivity and crossed-diagram
assembly are downstream of this umbrella. No exact disorder-averaged propagator,
SCBA/Ward closure, unconditional outgoing Hankel identity, or interchange of
zero-broadening, weak-disorder, ultraviolet and thermodynamic limits is asserted here.
-/
