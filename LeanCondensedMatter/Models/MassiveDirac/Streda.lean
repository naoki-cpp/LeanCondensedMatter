import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.TraceBridge
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.DisorderComparison
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.RadialIntegrand
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.Radial
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.RadialDenominator
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.LongitudinalSameSide
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.LongitudinalZeroBroadeningIntegral
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.HallZeroBroadeningIntegral
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.LongitudinalZeroBroadeningWeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.HallZeroBroadeningWeakDisorder
import LeanCondensedMatter.Models.MassiveDirac.Streda.BornLadder.HallZeroBroadeningProvenance
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.Trace
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RealSpace
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentGradientBridge
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentGradientDerivative
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentGradientSourceY
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.CurrentInPlaneResolvent
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RadialHarmonics
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RadialTrace
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.RealSpaceIntegral
import LeanCondensedMatter.Models.MassiveDirac.Streda.GaussianCrossed.ExplicitMoments

set_option linter.style.header false

/-!
# Massive-Dirac Středa response

Born-Dyson RA-dressed and bare same-side response, exact finite-disorder comparison,
polar momentum integration, and sequential fixed-cutoff zero-broadening and weak-disorder limits.
The separate Gaussian crossed `X/Ψ` sector supplies finite-radius real-space kernels with a
longitudinally dressed crossed current and explicit disorder weights.
Crossed Fourier blocks include the physical momentum measure; their conductivity normalization
must not attach it again. No crossed regulator limit or exact disorder realization is implied.
-/
