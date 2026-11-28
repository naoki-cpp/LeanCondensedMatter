import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.Green.RadialPauli
import LeanCondensedMatter.Models.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Models.MassiveDirac.Disorder.SingleParticleRate
import LeanCondensedMatter.Models.MassiveDirac.Disorder.TransportRate
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
import LeanCondensedMatter.Models.MassiveDirac.Disorder.TMatrix.BornDysonLoop
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Ladder.RegulatorBoundaryWeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Ladder.RegulatorBoundaryTransverseWeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Born.WeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Vertex.Born.InfiniteCutoff

set_option linter.style.header false

/-!
# Massive-Dirac scalar disorder

Scalar covariance, Born self-energy and scattering rates, Born-Dyson propagators, current ladders,
scalar T-matrices, and real-space Fourier representations.
Fixed-cutoff zero-broadening and weak-disorder limits are distinct from ultraviolet limits;
removing the Fourier cutoff at fixed self-energy cutoff does not prove a joint UV limit.
Neither exact disorder averaging nor an unconditional Hankel transform is asserted.
-/
