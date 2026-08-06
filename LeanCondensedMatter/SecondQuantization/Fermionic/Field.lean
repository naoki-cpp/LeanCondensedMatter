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
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StationaryFrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.InfiniteTimeFrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SpectralFrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ConductivityNormalization
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboGreenwood
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboBastinSpectral
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboBastinTrace
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaIntegration
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaOccupation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaCommonKernel
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StredaTraceRepresentation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.TransportConductivityBridge

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
self-adjoint directional current and proves their separate bounded response theorems. The
stationary layer rewrites the finite-time response exactly as a positive-lag transform and makes
the contact expectation time independent. The infinite-time layer proves the observation-time
limit at every positive switching rate. The spectral layer identifies that limit with the finite
pure-point Lehmann double sum plus the explicit geometric contact expectation. The final
normalization layer supplies a positive finite volume and the electric-field factor `-η + iω`,
turning the total-current vector-potential response into an intensive regularized conductivity.
The Kubo–Greenwood layer gives this derived finite spectral expression a public name, keeps
its diagonal, degenerate, contact, and regulator conventions explicit, and exposes it as the input
to the later Kubo–Bastin resolvent rewrite. The finite Bastin spectral layer converts the switching
rate to the energy broadening `ℏη`, proves the retarded resolvent action on the energy basis, and
rewrites every transition and the full conductivity without changing the contact term. The
ordinary-trace layer packages those finite resolvent coefficients into an energy-basis trace
carrier, proves its spectral expansion, and identifies the resulting named finite-dimensional
Kubo–Bastin conductivity with the upstream causal Kubo response. The Středa integration layer
records the additional finite-energy representation, derivative, integrability, and boundary
hypotheses required for integration by parts, names the regularized surface and sea contributions,
and proves their sum without assigning a magnetic-derivative interpretation. The occupation layer
then makes the first concrete spectral-to-energy bridge: a differentiable occupation is required to
reproduce the discrete pure-point probabilities, and every transition difference is rewritten as
an oriented integral of its energy derivative. The common-kernel layer localizes each transition
to its oriented spectral interval, combines the finite family into one globally integrable
piecewise energy kernel, and proves that its full-line integral is the current-current Bastin sum.
It deliberately stops before treating that discontinuous kernel as a differentiable Středa
primitive. The traced-representation layer inserts the smooth finite-dimensional ordinary-trace
surface primitive and residual sea kernel into the abstract integration data, proves that its
energy integral is the canonical occupation-weighted Bastin trace integral, and leaves equality
with any chosen response as an explicit hypothesis. The transport bridge reuses the general
finite-volume system convention without importing the fermionic model into the
dimension-independent transport layer.
-/
