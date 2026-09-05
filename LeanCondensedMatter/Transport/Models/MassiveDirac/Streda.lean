import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiberResponse
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the shared-provenance fixed-momentum Středa response matrix and the finite-`η`
Born-Dyson RA-dressed/bare-same-side Hall surface trace bridge. Pointwise trace identities and
finite-energy surface/sea integration are consumed directly from `Transport.Streda`. Physical
conductivity still requires the downstream Bastin prefactor and continuum momentum normalization.
Bounded-operator and spectral/resolvent infrastructure is owned by `MassiveDirac.Model`; ladder and
Born-Dyson Green construction remain owned by `MassiveDirac.Disorder`.
-/
