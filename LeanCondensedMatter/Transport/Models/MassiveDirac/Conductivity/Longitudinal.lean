import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.RelaxationTime

set_option linter.style.header false

/-!
# Massive-Dirac longitudinal transport

Public umbrella for longitudinal electrical conductivity of the two-dimensional massive Dirac
model. It currently exposes the zero-temperature relaxation-time benchmark.

Finite-broadening Born-Dyson vertex algebra remains owned by `MassiveDirac.Disorder`, while generic
Kubo–Bastin/Středa response identities remain owned by `Transport.Streda`. Model-specific routing
wrappers are not retained here unless they add a reusable conductivity-level result.
-/
