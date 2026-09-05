import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Basic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Kinematics
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Occupation
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Spectral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Interband
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral

set_option linter.style.header false

/-!
# Massive-Dirac model

Model-owned public umbrella for the matrix model, bounded-operator realization and in-plane current
API, radial kinematics, spectral occupation and Fermi-surface kinematics, spectral-projector and
interband algebra, and matrix/operator spectral realization. Canonical implementations live under
`Transport/Models/MassiveDirac/Model/`.
-/
