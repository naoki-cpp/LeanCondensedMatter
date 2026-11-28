import LeanCondensedMatter.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderZeroBroadening
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.FiniteBroadeningBornLadderProjection
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.GaussianCrossed
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.NonCrossing
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.NonCrossingDecomposition
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.NonCrossingMechanismClassification
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.CleanBastin
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall.Intrinsic

set_option linter.style.header false

/-!
# Massive-Dirac Hall conductivity

Physical Hall tensor projection, intrinsic and clean Bastin responses, and fixed-cutoff
Born-Dyson non-crossing Hall limits with intrinsic, side-jump and non-crossing skew classification.
The regulated Gaussian crossed `X/Ψ` conductivity is a distinct contribution; its normalization
uses the momentum measures already included in the Fourier blocks. No crossed limit or complete
Gaussian-disorder skew value follows from the non-crossing result.
-/
