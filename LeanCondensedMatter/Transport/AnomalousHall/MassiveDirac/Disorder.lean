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
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexFiniteCutoff
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexWeakDisorder
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.BornCurrentVertexTransportBridge
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
reduction, finite-cutoff integration of the resulting one-dimensional Green-product kernels, the
exact arctangent evaluation of the fully normalized finite-cutoff longitudinal `σₓ` current-rung
coefficient, and its fixed-cutoff metallic weak-disorder limit.  The resulting scalar ladder factor
is identified with the already-derived microscopic `τ_tr / τ_sp` factor.  The scalar and `σ_z`
damping channels remain separate through the Pauli algebra, while the common retarded-advanced
denominator product is exposed as a real sum of squares.

Kubo insertion, SCBA, simultaneous UV / zero-broadening limits, crossed diagrams, and a complete
conductivity theorem remain separate.
-/
