import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticLocalLeg
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticDiagram
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticDiagramWeight
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticWickExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticThermalAmplitude
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticThermalComponentFactorization

set_option linter.style.header false

/-!
# Bosonic quartic diagrammatics

This umbrella module exposes the bosonic quartic-diagram layer:

- quartic interaction labels and ordered vertex operators;
- local-leg operators, mode labels, free-energy shifts, and CCR constants;
- labelled quartic diagrams, vertex orders, and ordered pairing data;
- connected-component restriction, reassembly, and decomposition equivalence;
- coupling-weight, Dyson-sign, and scalar-prefactor factorization by connected component;
- convergence-aware free Gibbs Wick expansion for the flattened local legs of any finite list of
  quartic vertices;
- coefficientwise scalar amplitudes placing the free thermal pair kernel on each ordered quartic
  diagram pairing;
- connected-component factorization of the bosonic thermal pairing value and full coefficientwise
  ordered amplitude through the statistics-independent Common pair-product decomposition.

Graph and component proofs are inherited from the statistics-independent `Common.QuarticDiagram`
API. The thermal amplitude keeps its Gibbs-domain, deletion-closure, and first-pair recurrence
hypotheses explicit and does not yet claim ordered-simplex integration or a connected Dyson theorem.
-/
