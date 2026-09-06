import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadialDenominator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinal

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the finite-`η` Born-Dyson RA-dressed/bare-same-side Hall and longitudinal
surface responses. The Hall path is exposed from the pointwise trace bridge through finite-cutoff
polar momentum integration and explicit radial reduction; the longitudinal path is exposed from its
ladder-regularity boundary through the corresponding pointwise and finite-cutoff momentum response.
Generic shared-provenance response matrices, pointwise trace identities, and finite-energy
surface/sea integration are consumed directly from `Transport.Streda`.

Physical conductivity remains downstream: only `MassiveDirac.Conductivity` attaches the common
Bastin/Středa conductivity prefactor and physical continuum momentum normalization. Bounded-operator
and spectral/resolvent infrastructure is owned by `MassiveDirac.Model`; ladder and Born-Dyson Green
construction remain owned by `MassiveDirac.Disorder`.
-/
