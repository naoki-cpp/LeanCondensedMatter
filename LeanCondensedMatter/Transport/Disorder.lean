import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.Transport.Disorder.Resolvent
import LeanCondensedMatter.Transport.Disorder.AveragedSelfEnergy
import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Born
import LeanCondensedMatter.Transport.Disorder.Ladder
import LeanCondensedMatter.Transport.Disorder.SCBA
import LeanCondensedMatter.Transport.Disorder.Ward

set_option linter.style.header false

/-!
# Finite disorder transport API

Public umbrella for exact finite disorder ensembles, arbitrary-regulator disorder resolvents and
moments, the exact averaged-Green/self-energy bridge, first-Born self-energy, reusable
retarded-advanced covariance ladder algebra, the SCBA approximation layer, and its finite bounded
charge-vertex Ward bridge. Canonical implementations live under `Transport/Disorder/`.
-/
