import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.Response
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.Integral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiberResponse
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the model-specific Bastin/Středa trace identity, finite-energy surface/sea
decomposition, shared-provenance fixed-momentum response matrix, and the finite-`η` Born-Dyson
RA-dressed/bare-same-side Hall surface trace bridge. Physical conductivity still requires the
downstream Bastin prefactor and continuum momentum normalization. Bounded-operator and
spectral/resolvent infrastructure is owned by `MassiveDirac.Model`; ladder and Born-Dyson Green
construction remain owned by `MassiveDirac.Disorder`.
-/
