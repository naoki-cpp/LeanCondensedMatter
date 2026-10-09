import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalSlotSplit
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitConnectivity
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumComponents
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumPairImage
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.SlotSplit.SlotSplitVacuumComponentPair
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.SlotCongr
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Components.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalPiece
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalPiecePairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossingEven
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossingTimeLocality

set_option linter.style.header false

/-!
# Statistics-independent two-point diagrammatics

This package contains the combinatorial infrastructure for paired diagrams with two distinguished
one-legged external vertices and quartic interaction vertices. It does not attach operator
amplitudes or choose bosonic or fermionic statistics.

A special feature of the two-point family is that the two external vertices are automatically in
the same connected component: a component containing exactly one external leg would have an odd
number of legs and therefore could not carry a perfect pairing. Hence, for two-point diagrams,
external connectedness is equivalent to the absence of vacuum components.

The subpackages separate the main combinatorial responsibilities:

* `Core` defines the diagram syntax, flattened leg enumeration, vertex graph, and the semantic
  predicates for vacuum-free and externally connected diagrams.
* `Components` restricts connected components, identifies the canonical external component and
  vacuum components, and provides componentwise finite-sum and finite-product decompositions.
* `External` isolates the external component, splits its interaction slots from the vacuum
  remainder, and packages the resulting standalone external piece together with pairing transport.
* `SlotSplit` compares the ambient two-point diagram with the external/vacuum slot decomposition,
  transporting vacuum pairings and vacuum components to the corresponding quartic diagrams.
* `Mixed` transports the fixed pairing to mixed imaginary-time order and develops component-local
  positions, pairings, normalized-pair equivalences, crossing decompositions, parity, and
  fixed-order-chamber locality.

The representation is intentionally kept distinct from `ExternalInsertionDiagram`. The two
families share lower-level component and leg-data machinery, while the mature two-point API keeps
its own canonical normal forms for the downstream two-point expansion.
-/
