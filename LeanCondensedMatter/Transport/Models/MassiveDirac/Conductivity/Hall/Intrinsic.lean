import LeanCondensedMatter.Transport.Models.MassiveDirac.Model
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Bridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Berry.Symmetry
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic.Response
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic.Conductivity

set_option linter.style.header false

/-!
# Massive-Dirac intrinsic anomalous Hall response

Public umbrella for Berry-curvature bridges, symmetry, intrinsic response, and clean conductivity.
Berry geometry is owned by `MassiveDirac/Model/Berry/`; intrinsic response and conductivity live under `MassiveDirac/Conductivity/Hall/Intrinsic/`.
-/
