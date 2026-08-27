import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.ScalarCovariance
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Propagator

set_option linter.style.header false

/-!
# Massive-Dirac disorder transport

Public umbrella for the disorder-dependent phases of the massive-Dirac anomalous Hall program.
The current Phase 4 slice combines the exact finite scalar-covariance specialization with the shared
clean retarded/advanced Pauli-basis propagator API. Born/SCBA closure, continuum momentum
scattering, current-vertex resummation, and crossed diagrams remain separate.
-/
