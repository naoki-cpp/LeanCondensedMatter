import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentOrderDecomposition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.IntegratedComponentFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.AmplitudeFactorization

set_option linter.style.header false

/-!
# External/vacuum factorization of labelled two-point amplitudes

This is the assembly owner for the remaining finite-sum step of the external-leg linked-cluster
theorem. Global interaction orders are decomposed once into component-local orders and one shuffle;
the a.e. shuffle integral covariance is supplied by `IntegratedComponentFactorization`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

end Fermionic
end SecondQuantization
