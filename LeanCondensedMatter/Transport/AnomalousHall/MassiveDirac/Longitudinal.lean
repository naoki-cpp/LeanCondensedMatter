import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Longitudinal.RelaxationTime

set_option linter.style.header false

/-!
# Massive-Dirac longitudinal transport

Public umbrella for longitudinal electrical-response benchmarks of the two-dimensional massive
Dirac model.  The current implementation exposes the zero-temperature Fermi-surface relaxation-time
approximation; later Kubo/disorder work must derive its transport lifetime rather than identifying
it with a single-particle broadening by definition.
-/
