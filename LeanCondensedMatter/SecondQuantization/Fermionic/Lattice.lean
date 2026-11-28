import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedMatrixUnitAdjoint
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.PeierlsContact
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.HermitianBondCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricPeierls

set_option linter.style.header false

/-!
# Fermionic lattice operators

Second-quantized hopping Hamiltonians, bounded finite-lattice realizations and evolution,
Peierls currents and contacts, rank-one operators, and geometric current aggregation.
One-particle hopping geometry is provided by `Analysis.DiscreteLattice`.
-/
