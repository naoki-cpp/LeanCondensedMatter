import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.CleanBastin
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Massive-Dirac Hall conductivity

Public entry point for physically normalized Hall-conductivity results of the massive-Dirac
benchmark. The finite-`η` ordered `xy` Středa component is the source-`.y` specialization of the
source-indexed conductivity bridge owned by `MassiveDirac.Conductivity.FiniteBroadeningBornLadder`.
Formalism-specific analysis, including finite-`η` Středa momentum integration and radial reduction,
remains upstream under the corresponding Bastin/Středa owners; this layer exposes conductivity-level
results.
-/
