import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Longitudinal.RelaxationTime
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Longitudinal.FiniteBroadening

set_option linter.style.header false

/-!
# Massive-Dirac longitudinal transport

Public umbrella for longitudinal electrical response of the two-dimensional massive Dirac model.
It exposes both the zero-temperature relaxation-time benchmark and the exact finite-broadening
operator/channel bridge that keeps an in-plane dressed current vertex explicit inside the generic
Kubo–Bastin/Středa trace representation.

The finite-broadening layer does not identify the dressed vertex with the weak-disorder scalar
transport factor by definition.  A later ladder solution must be inserted through that operator
boundary before recovering the RTA benchmark under explicit approximation and limiting hypotheses.
-/
