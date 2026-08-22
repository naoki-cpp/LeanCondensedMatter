import LeanCondensedMatter.Transport.FiniteKuboBastin
import LeanCondensedMatter.Transport.OccupationInterpolation
import LeanCondensedMatter.Transport.KuboBastinOccupation
import LeanCondensedMatter.Transport.KuboBastinCommonEnergy

set_option linter.style.header false

/-!
# Kubo–Bastin transport API

Public umbrella for the generic finite regularized Kubo–Bastin layer and its occupation/common-energy
bridges. Resolvent identities live upstream; Středa decompositions and concrete model
specializations live downstream.
-/
