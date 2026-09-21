import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentPartition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Components.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentPairEquiv

set_option linter.style.header false

/-!
# Statistics-independent external-insertion diagrammatics

This package provides the paired diagram core for an even finite family of one-legged external
insertions and quartic interaction vertices, the external-supported/vacuum connected-component
split, generic component restriction, restriction of vacuum components to ordinary quartic
diagrams, and a component-local decomposition of normalized pairs. The core leg enumeration places
external insertions first and interaction legs afterward in increasing vertex/local-leg order,
providing a fixed ordered basis for later crossing/sign transport. Amplitude factorization remains
downstream work driven by concrete higher-point consumers.
-/
