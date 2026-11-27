import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramSumIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series.CauchySeries

set_option linter.style.header false

/-!
# Fermionic two-point diagram expansion

Finite-mode imaginary-time two-point Wick diagrams with quartic interaction vertices: Common-owned
mixed event/leg ordering, fermionic flattening and fixed-external amplitudes;
exchange of the finite diagram sum with the ordered-simplex integral; and the perturbative
two-point series. The physical Cauchy factorization is the two-external-leg specialization
of the arbitrary-external insertion theory.
-/
