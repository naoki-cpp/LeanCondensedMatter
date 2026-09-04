import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumBornAngularBridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.DenominatorUV
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexTransportBridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexInfiniteCutoff

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent massive-Dirac anomalous Hall benchmark. It exposes the
exact finite scalar-disorder specialization, the finite-cutoff continuum Born self-energy and its
broadening/UV limits, the microscopic single-particle and transport rates, and the retarded-advanced
current-vertex chain.

The finite-external-broadening Born-Dyson rung reduces through the shared polar Pauli algebra to an
in-plane coefficient pair `(X,Y)` with repository orientation `[[X,-Y],[Y,X]]`. Radial integration
attaches the scalar-disorder line and physical momentum measure exactly once before the pair is
consumed by the canonical in-plane ladder solution. The zero-external-broadening weak-disorder path
and its transport-lifetime bridge remain separate from the finite-`η` path.

Physical charge-current conversion and Kubo/Středa insertion are downstream. SCBA/Ward closure,
crossed diagrams, and simultaneous thermodynamic, UV, disorder, and zero-broadening limits are not
asserted here.
-/
