import LeanCondensedMatter.SecondQuantization.Common.Algebra
import LeanCondensedMatter.SecondQuantization.Common.Interaction
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Common.Thermal
import LeanCondensedMatter.SecondQuantization.Common.Perturbation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace
import LeanCondensedMatter.SecondQuantization.Fermionic.Field
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics

set_option linter.style.header false

/-!
# Second quantization

This is the single public entry point for the second-quantization hierarchy.

The implementation is owned by three explicit namespaces and directory trees:

- `SecondQuantization.Common` for statistics-independent algebra, interactions, imaginary-time,
  thermal, perturbative, and diagrammatic constructions;
- `SecondQuantization.Fermionic` for fermionic algebra, completed-space analysis, fields, finite
  transport adapters, thermal theory, perturbation theory, and diagrammatics;
- `SecondQuantization.Bosonic` for the convergence-aware bosonic algebra, thermal, perturbative, and
  diagrammatic line.

The former top-level import modules `SecondQuantization.Common`, `SecondQuantization.Fermionic`, and
`SecondQuantization.Bosonic` are intentionally not retained as compatibility surfaces. Import this
module for the full public API, or import a responsibility-specific leaf umbrella directly.
-/
