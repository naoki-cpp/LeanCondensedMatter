import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.CleanBastin
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Massive-Dirac Hall conductivity

Public entry point for physically normalized Hall-conductivity results of the massive-Dirac
benchmark. The finite-`η` ordered `xy` Středa component is the source-`.y` specialization of the
source-indexed conductivity bridge owned by `MassiveDirac.Conductivity.FiniteBroadeningBornLadder`;
its fixed-disorder zero-broadening boundary and subsequent one-sided weak-disorder limit are exposed
here as ordered components, still distinct from the antisymmetric Hall projection.

Formalism-specific analysis, including finite-`η` Středa momentum integration, radial reduction, and
zero-broadening/weak-disorder response limits, remains upstream under the corresponding Bastin/Středa
owners; this layer exposes conductivity-level results.
-/
