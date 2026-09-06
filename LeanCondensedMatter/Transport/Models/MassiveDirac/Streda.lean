import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderRadial

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the finite-`η` Born-Dyson RA-dressed/bare-same-side Hall surface response, from
the pointwise trace bridge through finite-cutoff polar momentum integration and explicit radial
reduction. Generic shared-provenance response matrices, pointwise trace identities, and finite-energy
surface/sea integration are consumed directly from `Transport.Streda`.

Physical conductivity remains downstream: only `MassiveDirac.Conductivity` attaches the common
Bastin/Středa conductivity prefactor and physical continuum momentum normalization. Bounded-operator
and spectral/resolvent infrastructure is owned by `MassiveDirac.Model`; ladder and Born-Dyson Green
construction remain owned by `MassiveDirac.Disorder`.
-/
