import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint

set_option linter.style.header false

/-!
# Statistics-independent diagrammatics

This package contains three statistics-independent diagram families.

* `Quartic` describes diagrams made only of four-legged interaction vertices, together with
  connected-component restriction, reassembly, pair decomposition, crossing parity, and scalar
  component factorization.
* `TwoPoint` adds two distinguished one-legged external vertices to quartic interaction vertices
  and provides the corresponding external/vacuum component decomposition, slot splitting,
  mixed-order pairing transport, and component factorizations.
* `ExternalInsertion` treats an arbitrary even family of one-legged external insertions together
  with quartic interaction vertices and provides generic external-supported/vacuum component
  semantics.

These representations share combinatorial primitives but are not definitionally identified.
Explicit equivalences and transports relate the structures that are proved to coincide.
-/
