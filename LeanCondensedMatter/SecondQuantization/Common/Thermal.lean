import LeanCondensedMatter.SecondQuantization.Common.Algebra.DiagonalTrace
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteTrace
import LeanCondensedMatter.SecondQuantization.Common.Algebra.FiniteHilbertOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GibbsExpectation
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalSector
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalFullFock
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CompletedResponse
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonicalSectorDecomposition
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalGrandCanonicalCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# Statistics-independent thermal states, occupation-basis formulas, and pairing expansions

The statistics-independent thermal theory separates five layers:

- algebraic diagonal traces and finite unnormalized weight sums;
- finite Hilbert realization of algebraic Fock operators and compatibility of completed-space
  Gibbs densities with their finite-Hilbert counterparts;
- the generic `QuantumTheory.Gibbs.Eigenbasis` density state and sharp-number canonical sector specialization;
- finite Gibbs trace-ratio and Boltzmann-coordinate formulas;
- the implementation-independent Bloch–de Dominicis expectation recursion and its finite Gibbs
  pairing specialization.

The normalized Gibbs density is the generic pure-point density operator. The Common thermal
layer supplies the Fock-space adapters, canonical and grand-canonical sector relations, and
trace-ratio coordinate formulas. The Bloch–de Dominicis recursion is independent of finiteness
of the configuration space. Its bosonic specialization uses explicit summability and
operator-domain hypotheses.
-/
