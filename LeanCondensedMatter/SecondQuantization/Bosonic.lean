import LeanCondensedMatter.SecondQuantization.Bosonic.Foundations
import LeanCondensedMatter.SecondQuantization.Bosonic.OperatorAlgebra
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal
import LeanCondensedMatter.SecondQuantization.Bosonic.BlochDeDominicis
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics

set_option linter.style.header false

/-!
# Bosonic second quantization

Umbrella module for the bosonic line of `SecondQuantization/`.

It imports:

- occupation-number foundations and the algebraic bosonic Fock space;
- creation/annihilation operators, CCR, exchange algebra, and number operators;
- free imaginary-time evolution and the algebraic interaction picture;
- convergence-aware free thermal series and two-point results;
- the uncutoff bosonic Bloch–de Dominicis two-point instantiation;
- quartic interaction and diagrammatics through connected-component decomposition and scalar-weight
  factorization.

The algebraic and finite-combinatorial layers share infrastructure with the fermionic line through
`SecondQuantization.Common`. General bosonic Gibbs expectations, Dyson coefficients, and full Wick
amplitudes are not exported here because they require additional summability or locally finite
operator hypotheses on the infinite occupation basis.
-/
