import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticLocalLeg
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticLegFamily
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticDiagram
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticDiagramWeight

set_option linter.style.header false

/-!
# Bosonic quartic diagrammatics

This umbrella module exposes the bosonic quartic-diagram layer that is currently independent of a
general bosonic Gibbs functional:

- quartic interaction labels and ordered vertex operators;
- local-leg operators, mode labels, free-energy shifts, and CCR constants;
- flattened time-evolved leg families;
- labelled quartic diagrams, vertex orders, and ordered pairing data;
- connected-component restriction, reassembly, and decomposition equivalence;
- coupling-weight, Dyson-sign, and scalar-prefactor factorization by connected component.

Graph and component proofs are inherited from the statistics-independent `Common.QuarticDiagram`
API. This module does not yet define a full bosonic Wick-diagram amplitude or Dyson diagram expansion;
those require a convergence-aware bosonic expectation and operator-integration layer.
-/
