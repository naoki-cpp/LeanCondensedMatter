import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac

set_option linter.style.header false

/-!
# Anomalous Hall transport benchmarks

Public entry point for clean and disordered anomalous-Hall model benchmarks.  Generic spectral and
linear-response infrastructure remains owned by `Analysis` and the generic `Transport` leaves;
this namespace contains concrete transport models that consume those layers.
-/
