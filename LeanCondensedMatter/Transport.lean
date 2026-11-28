import LeanCondensedMatter.Transport.Core
import LeanCondensedMatter.Transport.Topology
import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.Transport.FiniteConductivityTable.Eigenbasis
import LeanCondensedMatter.Transport.Reciprocity.Data
import LeanCondensedMatter.Transport.Reciprocity.Kubo
import LeanCondensedMatter.Transport.KuboSymmetry.FiniteTime
import LeanCondensedMatter.Transport.Scattering.IsotropicAngularWeights
import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.KuboBastin
import LeanCondensedMatter.Transport.Streda
import LeanCondensedMatter.Transport.Disorder

set_option linter.style.header false

/-!
# Transport

Model-independent conductivity, reciprocity and Kubo symmetry, periodic Bloch data,
finite spectral tables, resolvents, Kubo–Bastin and Středa responses, isotropic scattering,
and finite-disorder theory. Concrete Hamiltonian benchmarks belong to `Models`.
-/
