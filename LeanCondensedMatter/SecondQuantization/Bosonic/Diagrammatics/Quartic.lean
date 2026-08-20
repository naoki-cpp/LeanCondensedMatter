import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Diagram
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.WickExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Amplitude
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.ComponentFactorization
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Thermal.Connected

set_option linter.style.header false

/-!
# Bosonic quartic diagrammatics

This umbrella module exposes the bosonic quartic-diagram layer:

- quartic interaction labels and ordered vertex operators;
- local-leg operators, mode labels, free-energy shifts, and CCR constants;
- labelled quartic diagrams, vertex orders, and ordered pairing data;
- connected-component restriction, reassembly, and decomposition equivalence;
- convergence-aware free Gibbs Wick expansion for the flattened local legs of any finite list of
  quartic vertices;
- coefficientwise scalar amplitudes placing the free thermal pair kernel on each ordered quartic
  diagram pairing;
- connected-component factorization of the bosonic thermal pairing value and full coefficientwise
  ordered amplitude through the statistics-independent Common pair-product and scalar-prefactor
  decompositions;
- order-averaged diagram amplitudes, their multiplicative connected decomposition, and the resulting
  coefficientwise cumulant-equals-connected-diagram theorem.

Graph, component, scalar vertex-weight, and cumulant combinatorics are inherited from the
statistics-independent Common and Combinatorics APIs. The thermal expectation layer keeps its
Gibbs-domain, deletion-closure, and first-pair recurrence hypotheses explicit. The connected theorem
exposed here is coefficientwise and does not claim infinite-series/completed-space analytic
convergence.
-/
