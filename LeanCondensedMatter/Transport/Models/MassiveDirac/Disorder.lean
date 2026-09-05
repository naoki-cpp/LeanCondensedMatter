import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.SelfEnergy
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Denominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.Damping
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornInvertibility
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexRung
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornCurrentVertexInfiniteCutoff

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent massive-Dirac transport benchmark. The continuum Born
chain is organized by physical and analytic responsibility: `Born.SelfEnergy` owns the finite-cutoff
self-energy and its polar provenance, `Born.Denominator` owns exact denominator evaluation and its
UV/broadening limits, and `Born.Damping` owns the channel limits and upper-band damping projection.

The finite-external-broadening Born-Dyson rung reduces through the shared polar Pauli algebra to an
in-plane coefficient pair `(X,Y)` with repository orientation `[[X,-Y],[Y,X]]`. Radial integration
attaches the scalar-disorder line and physical momentum measure exactly once before the pair is
consumed by the canonical in-plane ladder solution. For the zero-external-broadening Born route,
`BornCurrentVertexRung` owns the exact normalized finite-cutoff longitudinal rung, while the
fixed-cutoff weak-disorder and infinite-cutoff limits remain separate downstream routes.

Physical charge-current conversion and Kubo/Středa insertion are downstream. SCBA/Ward closure,
crossed diagrams, and simultaneous thermodynamic, UV, disorder, and zero-broadening limits are not
asserted here.
-/
