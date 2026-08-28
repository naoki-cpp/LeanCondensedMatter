import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.CurrentBridge
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Kinematics
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Occupation
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.FermiSurfaceKinematics
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Spectral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.OperatorSpectral

set_option linter.style.header false

/-!
# Massive-Dirac model

Public umbrella for the matrix model, bounded-operator realization, current bridge, radial
kinematics, spectral occupation and Fermi-surface kinematics, and matrix/operator
spectral-projector algebra. Canonical implementations live under `MassiveDirac/Model/`.
-/
