import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.RelaxationTime
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.FiniteBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal.FiniteBroadeningBornLadder

set_option linter.style.header false

/-!
# Massive-Dirac longitudinal transport

Public umbrella for longitudinal electrical response of the two-dimensional massive Dirac model.
It exposes the zero-temperature relaxation-time benchmark, the exact finite-broadening operator/
channel bridge that keeps an in-plane dressed current vertex explicit inside the generic
Kubo–Bastin/Středa trace representation, and the physical current obtained by inserting the solved
finite-`η` Born-Dyson ladder coefficients into that existing operator boundary.

The finite-broadening ladder solution remains distinct from its later Kubo/Středa insertion and from
weak-disorder or zero-broadening limits.  In particular, no scalar transport factor is substituted
for the two-component solved vertex by definition.
-/
