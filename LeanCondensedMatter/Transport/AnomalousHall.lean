import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin

set_option linter.style.header false

/-!
# Anomalous Hall transport benchmarks

Public entry point for anomalous-Hall model benchmarks. Generic spectral, intrinsic-current,
linear-response, Kubo–Bastin, Středa, and disorder infrastructure remains owned upstream.

The massive-Dirac benchmark is exposed through four logical layers:

- `MassiveDirac.Model` — Hamiltonian, current realization, and spectral/projector algebra;
- `MassiveDirac.Intrinsic` — Berry bridge and clean intrinsic Hall conductivity;
- `MassiveDirac.Streda` — bounded-operator specialization of the generic Středa API;
- `MassiveDirac.Bastin` — detailed finite-/zero-broadening Bastin analysis.

Reusable analysis currently living in the final layer is being extracted upstream under #1596.
-/
