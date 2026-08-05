import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FiniteParticleFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Mode
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SecondQuantizationLinearity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SecondQuantizationCommutator
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Peierls
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.BoundedKuboBridge

set_option linter.style.header false

/-!
# Fermionic fields

Basis-independent fermionic finite-particle Fock spaces, smeared fields, second quantization, and
continuity-derived currents. The completed F2 layer contains creation and annihilation fields,
smeared and mode CAR, and the basis-induced equivalence with the occupation-subset representation.
The F3 layer defines the algebraic second-quantization map `dGamma`, proves its linearity and
commutator functoriality, and identifies total particle number as `dGamma id`. The initial F4 layer
defines smeared charge density and its algebraic Heisenberg commutator identity. The F5 lattice
layer starts directly on arbitrary site types with row-and-column locally finite hopping, rather
than assuming a finite lattice. The F6 layer introduces oriented Peierls link phases and proves
that the continuity-derived bond current is minus the algebraic weak derivative of the
Peierls-coupled link Hamiltonian at zero gauge field. The F7 bridge restricts only at the response
boundary to a finite site cutoff, transports the complete fermionic Fock space to a finite Hilbert
space, and exposes the derived bond current as a bounded observable accepted by the general Kubo
API.
-/
