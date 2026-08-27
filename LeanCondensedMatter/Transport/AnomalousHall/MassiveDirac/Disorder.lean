import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ContinuumBornAngularBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.PropagatorSymmetry

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent phases of the massive-Dirac anomalous Hall program.
The current Phase 4 slice keeps the exact finite scalar-covariance specialization separate from the
model-specific finite-cutoff continuum Born closure, while sharing the clean Pauli-basis propagator
and exact momentum-inversion symmetry.  The continuum closure now includes an explicit full-angle
polar Green integral proving the `2π` radial-reduction factor rather than inferring it from inversion
symmetry alone.  UV and zero-broadening limits, scattering-rate extraction, SCBA, current-vertex
resummation, and crossed diagrams remain separate.
-/
