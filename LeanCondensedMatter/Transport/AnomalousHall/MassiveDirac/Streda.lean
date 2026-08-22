import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStreda
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaIntegral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracCurrentOperatorBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDiracStredaSpectral

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the bounded-operator realization of the massive-Dirac model and its concrete
specialization of the generic finite Bastin/Středa transport API.

Detailed pole extraction, radial limit interchange, and final zero-temperature Bastin analysis remain
downstream in `MassiveDirac.Bastin`.
-/
