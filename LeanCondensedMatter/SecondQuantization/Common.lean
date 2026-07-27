import LeanCondensedMatter.SecondQuantization.Common.Algebra
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Common.Thermal
import LeanCondensedMatter.SecondQuantization.Common.Perturbation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics

set_option linter.style.header false

/-!
# Statistics-independent second quantization

The shared API is organized into five responsibility-based umbrellas:

- `Algebra`: algebraic Fock infrastructure, statistics, grading, and CAR/CCR interfaces;
- `ImaginaryTime`: time ordering, diagonal evolution, interaction pictures, and KMS rotation;
- `Thermal`: normalized functionals, finite/summability-aware traces, and Bloch–de Dominicis;
- `Perturbation`: coefficientwise operator integration on finite configuration types;
- `Diagrammatics`: quartic diagrams and connected-component decomposition.

The first, second, third, and fifth groups align with the statistics-specific public layouts where the
mathematics actually matches. `Perturbation` is explicitly finite-basis infrastructure and therefore
has no current bosonic counterpart.

`Common/` imports neither `Fermionic/` nor `Bosonic/`. General facts that do not mention algebraic
Fock spaces, statistics, or diagram data are placed upstream in `Analysis/` or `Combinatorics/`.
-/
