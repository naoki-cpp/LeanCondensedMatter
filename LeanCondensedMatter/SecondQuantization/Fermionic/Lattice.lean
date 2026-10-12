import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Spinful
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
It owns concrete discrete hopping and second-quantized currents, Peierls families, finite-lattice
bounded realizations, Hermiticity/current equivalences, and geometric current aggregation. The
statistics-independent site geometry and bond coordinates live in `QuantumMechanics.SingleParticle`. Generic Kubo, frequency-response, conductivity, Středa,
disorder, and validation mathematics do not belong to this layer. Response specializations consume
these model operators from downstream `Fermionic.Transport` modules.
-/
