import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ContinuumBornAngularBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorFactorization
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorEvaluation
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorUV
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ChannelBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SelfEnergyBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.UpperBandDamping
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SingleParticleRate
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.TransportRate
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornPropagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.CurrentVertexAngular
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexRadial
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexIntegral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.PropagatorSymmetry

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent phases of the massive-Dirac anomalous Hall program.
The completed Phase 4 chain keeps the exact finite scalar-covariance specialization separate from
the model-specific finite-cutoff continuum Born closure, while sharing the clean Pauli-basis
propagator and exact momentum-inversion symmetry.  It evaluates the common finite-cutoff radial
denominator, separates ultraviolet-sensitive real and metallic on-shell imaginary pieces, projects
the damping onto the upper band, derives the microscopic single-particle scattering rate, and
separately derives the Born transport rate from the Fermi-circle current-relaxation weight.

Phase 5 includes the exact finite-broadening angular reduction of the retarded-advanced `x`-current
rung, the weak-disorder Born-dressed Pauli propagator data, the Born-dressed angular/radial rung
reduction, and the exact finite-cutoff arctangent evaluation of its common radial denominator
integral.  The scalar and `σ_z` damping channels remain separate through the Pauli algebra, while
the common retarded-advanced denominator product is exposed as a real sum of squares.  The radial
cutoff is removed by a separate convergent `pMax → +∞` theorem at positive Born width.  The full
polar-angle Born rung keeps the transverse sign tied explicitly to the shared
`Transport.Disorder.Ladder` convention `Gᴿ Γ Gᴬ`.

The weak-disorder/on-shell coefficient limit, ladder resummation, identification with the Born
transport lifetime, SCBA, crossed diagrams, and a complete conductivity theorem remain separate.
-/
