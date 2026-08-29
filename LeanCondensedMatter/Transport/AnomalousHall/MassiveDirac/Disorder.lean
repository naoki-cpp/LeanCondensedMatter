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
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.CurrentVertexAngular
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
the damping onto the upper band, and derives the microscopic single-particle scattering rate.

Phase 5 begins with the finite-broadening retarded-advanced current rung.  Its model-specific Pauli
algebra is kept separate from radial integration and ladder resummation, while the operator order is
aligned with the shared `Transport.Disorder.Ladder` convention `Gᴿ Γ Gᴬ`.

Transport-lifetime identification, renormalization, SCBA, current-vertex resummation, simultaneous
UV / zero-broadening limits, and crossed diagrams remain separate.
-/
