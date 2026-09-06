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

Finite-broadening Born-Dyson propagator and vertex algebra remain owned by `MassiveDirac.Disorder`.
The model-specific pointwise Středa response and finite-cutoff polar momentum integration are owned
upstream by `MassiveDirac.Streda`, while generic retarded-advanced trace identities remain owned by
`Transport.Streda`. The conductivity layer starts only where the common static Bastin/Středa
conductivity prefactor and physical continuum momentum normalization are attached, or where an
upstream lifetime is connected to an actual conductivity benchmark.
-/
