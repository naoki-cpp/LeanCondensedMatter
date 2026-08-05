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
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.PeierlsContact
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeometricCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeometricPeierls
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.HarmonicSourceResponse

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
API. The subsequent transport layer differentiates the Peierls current itself, identifies its
contact operator, and combines the retarded current-current response with the explicit contact
term. The geometric layer derives bond-current self-adjointness from Hermitian hopping, aggregates
oriented bond observables into spatial current components, and proves that the directional current
and squared-coordinate contact arise respectively from differentiating the uniform-direction
Peierls Hamiltonian and its source-dependent current. The frequency-response layer keeps
observation time, adiabatic switching, and driving frequency as independent regulators and records
the possible orders of their limits explicitly. The harmonic-source layer realizes the complex
adiabatic coefficient through two physical real source quadratures coupled to the same
self-adjoint directional current and proves their separate bounded response theorems.
-/
