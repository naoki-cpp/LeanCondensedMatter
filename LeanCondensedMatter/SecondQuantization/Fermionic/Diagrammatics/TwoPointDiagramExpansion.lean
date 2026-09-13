import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Factorization.TwoPointLegEmbedding
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairImage
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Factorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series

set_option linter.style.header false

/-!
# Fermionic two-point diagram expansion

Finite-mode imaginary-time two-point Wick diagrams with quartic interaction vertices: Common-owned
mixed event/leg ordering, quartic-to-two-point leg embeddings, slot-split vacuum pairing and
vacuum-pair image transport, and binary slot-shuffle coordinates; fermionic flattening and
fixed-external amplitudes; external/vacuum component restriction and factorization;
external-component restriction; exchange of the finite diagram sum with the ordered-simplex
integral; and the perturbative two-point series assembled from the order-`n` coefficients.
-/
