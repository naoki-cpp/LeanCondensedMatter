import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics

set_option linter.style.header false

/-!
# Bosonic second quantization

The public bosonic API is organized into four layers:

- `Bosonic.Algebra`: occupation states, algebraic Fock space, creation/annihilation, CCR, grading,
  and number operators;
- `Bosonic.ImaginaryTime`: time ordering, free diagonal evolution, and the algebraic interaction
  picture;
- `Bosonic.Thermal`: convergence-aware free thermal sums, two-point coefficients, and the bosonic
  two-point Bloch–de Dominicis specialization;
- `Bosonic.Diagrammatics`: quartic vertices and statistics-independent diagram combinatorics through
  connected-component scalar-prefactor factorization.

Small implementation files remain grouped below these four umbrellas. General bosonic Gibbs
functionals, Dyson coefficients, and full Wick amplitudes are still blocked on summability-aware
interfaces for the infinite occupation basis.
-/
