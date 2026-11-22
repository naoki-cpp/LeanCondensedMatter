import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.Green
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
# Massive-Dirac scalar disorder

Umbrella for finite-ensemble scalar covariance; continuum Born self-energy,
damping and scattering times; finite-regulator Born-Dyson propagators and
current-vertex ladders; scalar-impurity T-matrices; and real-space Fourier
analysis. Definitions and proofs reside in the imported modules.

Fixed-cutoff zero-broadening boundaries, weak-disorder limits, and ultraviolet
limits are distinct. In particular, removing the outer Fourier cutoff at a
fixed Born self-energy cutoff does not establish a joint-cutoff UV limit.

Kubo/Středa conductivity and crossed-diagram assembly are downstream. No exact
disorder average, SCBA/Ward closure, unconditional outgoing Hankel identity,
or interchange of regulator, disorder, UV, and thermodynamic limits is claimed.
-/
