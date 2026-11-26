import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.TwoPointLegEmbedding
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairImage
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramSumIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series.CauchySeries

set_option linter.style.header false

/-!
# Fermionic two-point diagram expansion

Finite-mode imaginary-time two-point Wick diagrams with quartic interaction vertices: Common-owned
mixed event/leg ordering, quartic-to-two-point leg embeddings, slot-split vacuum pairing and
vacuum-pair image transport; fermionic flattening and
fixed-external amplitudes;
exchange of the finite diagram sum with the ordered-simplex integral; and the perturbative
two-point series. The physical Cauchy factorization now specializes the arbitrary-external
insertion theory rather than maintaining a separate two-point fiber/shuffle proof chain.
-/
