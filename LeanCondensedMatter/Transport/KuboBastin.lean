import LeanCondensedMatter.Transport.KuboBastin.PurePoint
import LeanCondensedMatter.Transport.KuboBastin.Finite
import LeanCondensedMatter.Transport.KuboBastin.FiniteTrace
import LeanCondensedMatter.Transport.KuboBastin.OccupationInterpolation
import LeanCondensedMatter.Transport.KuboBastin.Occupation
import LeanCondensedMatter.Transport.KuboBastin.CommonEnergy

set_option linter.style.header false

/-!
# Kubo–Bastin transport API

Public umbrella for pure-point Kubo–Bastin transition algebra, finite spectral-index responses,
occupation interpolation, and the occupation/common-energy bridges. `FiniteTrace` is retained only
as a declaration-free compatibility shim; genuine ordinary operator traces belong to the canonical
static Bastin/Středa layer under `Transport.Streda`.
-/
