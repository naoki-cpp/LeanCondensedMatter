import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Basic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Kinematics
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Occupation
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Spectral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Interband
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry

set_option linter.style.header false

/-!
# Massive-Dirac model

Model-owned public umbrella for the matrix model, bounded-operator realization and in-plane current
API, radial kinematics, spectral occupation and Fermi-surface kinematics, spectral-projector and
interband algebra, matrix/operator spectral realization, and Berry geometry with occupation-weighted
Berry response. Canonical implementations live under `Transport/Models/MassiveDirac/Model/`.
-/
