import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderWeakDisorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderProjection
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.GaussianCrossed
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.NonCrossing
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.NonCrossingDecomposition
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.NonCrossingMechanismClassification
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.CleanBastin
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Massive-Dirac Hall conductivity

Public entry point for physically normalized Hall-conductivity results of the massive-Dirac
benchmark. The finite-`η` Středa conductivity is represented directly as a
`ConductivityTensor (Fin 2)`, with measured-current and source directions as its two component
indices. Rotational closure proves the ordered `yx = -xy` and `yy = xx` relations before limits are
taken. After the componentwise zero-broadening boundary is formed, the antisymmetric Hall projection
of the resulting tensor is exactly the ordered `xy` component. The subsequent one-sided weak-disorder
limit is exposed both in `ℏ` normalization and in the standard Ado non-crossing `e²/h` form.

The Ado Eq. (12a-c) decomposition is connected theorem-by-theorem to the concrete ordered-`xy`
ladder provenance. After conductivity normalization, the `r_y Γ_x` contribution is the intrinsic
piece plus three quarters of the side-jump-type piece, while the `r_x Γ_y` contribution is the
remaining quarter of the side-jump-type piece plus the Gaussian-skew-type piece. These mechanism
names remain theorem-level classifications rather than primitive conductivity definitions.

The Gaussian crossed `X/Psi` route remains distinct from the non-crossing ladder. Its regulated
real-space Fourier blocks carry their physical momentum measures upstream, so the conductivity
boundary attaches only the two physical current scales and the trace-only Bastin prefactor.
Evaluation of the crossed scalar kernels and their regulator limits remains downstream.

Formalism-specific analysis, including finite-`η` Středa momentum integration, radial reduction, and
zero-broadening/weak-disorder response limits, remains upstream under the corresponding Bastin/Středa
owners; this layer exposes conductivity-level results. Non-Gaussian `C3` contributions remain a
separate downstream extension.
-/
