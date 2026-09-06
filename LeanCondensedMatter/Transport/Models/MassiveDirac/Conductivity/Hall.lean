import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.CleanBastin
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Normalization

set_option linter.style.header false

/-!
# Massive-Dirac Hall conductivity

Public entry point for physically normalized Hall-conductivity results of the massive-Dirac
benchmark. Formalism-specific analysis remains upstream under the corresponding Bastin/Středa
owners; this layer attaches the physical conductivity normalization and exposes final Hall results.
-/
