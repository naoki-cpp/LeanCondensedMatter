import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ContinuumBornAngularBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorFactorization
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorEvaluation
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorUV
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.DenominatorBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ChannelBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.SelfEnergyBroadeningLimit
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.PropagatorSymmetry

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent phases of the massive-Dirac anomalous Hall program.
The current Phase 4 slice keeps the exact finite scalar-covariance specialization separate from the
model-specific finite-cutoff continuum Born closure, while sharing the clean Pauli-basis propagator
and exact momentum-inversion symmetry.  The continuum closure includes an explicit full-angle polar
Green integral proving the `2π` radial-reduction factor, factors its surviving scalar and `σ_z`
channels through one common finite-cutoff radial denominator integral, evaluates that shared
integral by a principal complex-log endpoint formula, separates its exact finite-broadening real and
imaginary parts into logarithmic norm and principal-argument differences, exposes the real-part
cutoff dependence through the corresponding quartic real denominator polynomial, proves the
resulting logarithmic ultraviolet divergence of the real part at fixed nonzero broadening, takes the
metallic positive-broadening limit of the shared imaginary part separately at fixed finite cutoff,
propagates that limit through the existing scalar and `σ_z` Born channel factorization while proving
the scalar `η Re J_s` cross term vanishes, and lifts those channel limits through the existing
continuum disorder/measure prefactor to the scalar and `σ_z` self-energy damping coefficients.
Scattering-rate and lifetime identification, upper-band on-shell projection, renormalization, SCBA,
current-vertex resummation, simultaneous UV / zero-broadening limits, and crossed diagrams remain
separate.
-/
