import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracSpectral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerryBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBerrySymmetry
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracIntrinsicConductivity
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStreda
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSpectral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinBerry
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinBands
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracBastinLimit

set_option linter.style.header false

/-!
# Anomalous Hall transport benchmarks

Public entry point for clean and disordered anomalous-Hall model benchmarks.  Generic spectral and
linear-response infrastructure remains owned by `Analysis` and the generic `Transport` leaves;
this namespace contains concrete transport models that consume those layers.
-/
