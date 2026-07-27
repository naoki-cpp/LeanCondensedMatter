import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics

set_option linter.style.header false

/-!
# Fermionic second quantization

The public fermionic API is organized into five umbrellas:

- `Algebra`: occupation states, Fock space, CAR, exchange algebra, and Hamiltonians;
- `ImaginaryTime`: free evolution and the interaction picture;
- `Thermal`: finite-basis Gibbs expectations, free thermal functions, and Bloch–de Dominicis results;
- `Perturbation`: formal partition-series logarithms and finite-basis Dyson coefficients;
- `Diagrammatics`: quartic Wick diagrams, amplitudes, and the Dyson diagram expansion.

The first, second, third, and fifth groups parallel the bosonic public layout. `Perturbation` remains a
fermionic-only group because its current operator integrals and traces use the finite occupation basis.
-/
