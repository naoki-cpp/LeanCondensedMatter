import LeanCondensedMatter.Analysis.Operator.BerryGeometry.Connection
import LeanCondensedMatter.Analysis.Operator.BerryGeometry.Curvature

set_option linter.style.header false

/-!
# Berry geometry

Public routing module for finite-dimensional, pointwise Berry geometry. It exposes the shared
`BerryGeometry.PointwiseEigenbasisData` API, its simple-spectrum constructor, Berry connection,
Berry curvature, and the Hamiltonian-derivative / force-matrix identities built from them.

This route is intentionally separate from `Analysis.Operator.Spectral`: generic compact spectral,
eigenvector, and resolvent consumers do not need parameter-direction Berry geometry.
-/
