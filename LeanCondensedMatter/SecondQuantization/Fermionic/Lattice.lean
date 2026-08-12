import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Peierls
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedMatrixUnitAdjoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.PeierlsContact
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.HermitianBondCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricPeierls

set_option linter.style.header false

/-!
# Fermionic lattice models

Canonical lattice/model layer downstream of `Fermionic.Algebra` and upstream of response/transport.
It owns discrete lattice states, locally finite hopping, charge and bond currents, Peierls families,
finite-lattice bounded realizations, Hermiticity/current equivalences, and geometric aggregation.
Generic Kubo, frequency-response, conductivity, Středa, disorder, and validation mathematics do not
belong to this layer. Response specializations consume these model operators from downstream
`Fermionic.Field` or `Fermionic.Transport` modules. This umbrella is the public canonical import for
fermionic lattice/model constructions; downstream consumers explicitly open or qualify the
`Lattice` namespace rather than relying on the former `Field` ownership. The old `Fermionic.Field`
lattice module paths are intentionally not retained as forwarding modules.
-/
