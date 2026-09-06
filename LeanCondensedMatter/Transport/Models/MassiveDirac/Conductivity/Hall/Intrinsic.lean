import LeanCondensedMatter.Transport.Models.MassiveDirac.Model
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Bridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Symmetry
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Occupation
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic.Conductivity

set_option linter.style.header false

/-!
# Massive-Dirac intrinsic anomalous Hall response

Public umbrella for Berry-curvature bridges, symmetry, occupation-derived Berry weight, and clean
conductivity. Berry geometry and occupation-weighted Berry analysis are owned by
`MassiveDirac/Model/Berry/`; physical conductivity lives under
`MassiveDirac/Conductivity/Hall/Intrinsic/`.
-/
