import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ContinuumBorn
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.PropagatorSymmetry

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent phases of the massive-Dirac anomalous Hall program.
The current Phase 4 slice keeps the exact finite scalar-covariance specialization separate from the
model-specific finite-cutoff continuum Born closure, while sharing the clean Pauli-basis propagator
and exact momentum-inversion symmetry.  UV and zero-broadening limits, scattering-rate extraction,
SCBA, current-vertex resummation, and crossed diagrams remain separate.
-/
