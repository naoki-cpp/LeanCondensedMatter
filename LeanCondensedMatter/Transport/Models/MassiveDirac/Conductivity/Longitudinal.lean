import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.RelaxationTime
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.BornRelaxationTime
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.BornDysonStreda

set_option linter.style.header false

/-!
# Massive-Dirac longitudinal transport

Public umbrella for longitudinal electrical conductivity of the two-dimensional massive Dirac
model. It exposes the zero-temperature relaxation-time benchmark, its microscopic Born transport-
lifetime specialization, and the finite-cutoff finite-`η` Born-Dyson Středa surface conductivity
bridge.

Finite-broadening Born-Dyson propagator and vertex algebra remain owned by `MassiveDirac.Disorder`,
while generic retarded-advanced Středa trace identities remain owned by `Transport.Streda`. The
conductivity layer starts only where those canonical upstream objects are integrated over the
physical momentum measure or connected to an actual conductivity benchmark.
-/
