import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Response
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Integral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Matrix

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the model-specific Bastin/Středa trace identity, finite-energy surface/sea
decomposition, and shared-provenance fixed-momentum response matrix. Physical conductivity still
requires the downstream Bastin prefactor and continuum momentum normalization. Bounded-operator and
spectral/resolvent infrastructure is owned by `MassiveDirac.Model`.
-/
