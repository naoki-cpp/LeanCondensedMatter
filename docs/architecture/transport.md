# Transport ownership

Generic transport theory is upstream of concrete models. This note records stable ownership
boundaries; implementation history belongs in Git history, not here.

## Public routes

```text
LeanCondensedMatter.Analysis
        ↓
LeanCondensedMatter.Transport
        ├── Core
        ├── Resolvent
        ├── KuboBastin
        ├── Streda
        └── Disorder

LeanCondensedMatter.Transport.Analysis   (opt-in analytical utilities)

LeanCondensedMatter.Models
        ├── MassiveDirac
        ├── Parabolic2DEG
        └── RashbaExchange
```

`LeanCondensedMatter.Transport` does not import concrete `Models` or the opt-in
`Transport.Analysis` package. Representation-independent analysis such as finite-dimensional trace,
generic spectral resolvent algebra, and Lorentzian analysis stays under `LeanCondensedMatter.Analysis`.
`Analysis.Operator.FiniteTrace` owns the continuous ordinary trace, cyclicity, matrix/operator
transport, and differentiation laws. Transport consumers attach response meaning and normalization
separately; the trace module has no disorder or conductivity semantics.

## Generic owners

```text
Transport/
├── Core/          physical volume, normalization, conductivity tensor
├── FiniteConductivityTable.lean
│                  finite Lehmann + contact + positive-volume E-field normalization
├── FiniteConductivityTable/Eigenbasis.lean
│                  statistics-independent eigenbasis/channel-to-scalar adapter
├── Resolvent/     signed spectral regulator, physical spectral sides, self-energy algebra
├── Spectral/      response-neutral adapters from supplied spectral data to resolvent algebra
├── Analysis/      occupations, 2D continuum measure, angular harmonics, polar Fourier, relaxation time
├── KuboBastin/    Lehmann-to-resolvent response algebra and finite spectral sums
├── Streda/        static response kernels, traces, integration, response matrices
└── Disorder/      exact finite disorder, Green operators, Born, SCBA, ladder algebra
```

`Core.ConductivityNormalization` owns both the model-independent `PositiveVolume` datum and
the finite-volume electric-field conversion. Consumers use that owner directly; the underlying
volume is independent of Hilbert-space dimension or a particular response representation.

The zero-frequency normalization identity also belongs to `Core.ConductivityNormalization`.
The fermionic normalization module consumes channel response and observation-time convergence
without importing an eigenbasis representation. Its spectral conductivity identities belong to
the consuming `Fermionic.Transport.KuboGreenwood` module, whose final conductivity identification
uses the generic eigenbasis Lehmann theorem directly. `Fermionic.Transport.KuboBastinSpectral`
identifies the causal conductivity with the spectral Bastin representation at arbitrary frequency
and positive switching rate. Static consumers set the frequency to zero in that same representation;
this does not take a zero-switching or DC limit. Fermionic common-energy and spectral conductivity
use the generic channel response and vertex-term identities directly.

`FiniteConductivityTable.Eigenbasis` constructs the scalar data from a supplied eigenbasis and
`ResponseChannel`: measured and source operators supply the two Lehmann matrix factors, while
the observable variation supplies the contact expectation. The scalar table/evaluator module
remains independent of operator data and channel construction. Neither module depends on particle
statistics, Fock space, lattice geometry, or a concrete current realization.

The Greenwood definition evaluates this generic data with `finiteConductivityTableValue`, supplying
only the fermionic charge-current channel. Its finite spectral index is required by the evaluator;
`finiteConductivityTableValue_ofEigenbasis` identifies the result with the aggregate Lehmann
response plus contact and the explicit normalization. The scalar evaluation and Bastin conversion
consume the aggregate identities without expanding individual transitions downstream.

The main semantic boundaries are:

- finite spectral index and finite Hilbert-space dimension are separate assumptions;
- ordinary operator trace is introduced only where an operator-valued kernel is traced;
- Středa response matrices are response-level objects, not physical conductivity tensors;
- physical prefactors, volume or continuum normalization, and limiting procedures remain explicit
  before constructing a `Core.ConductivityTensor`;
- `FiniteConductivityTable` is an electrical-conductivity adapter downstream of the generic
  `QuantumTheory.LinearResponse.FiniteLehmannTable`; the generic Lehmann evaluator does not depend
  on contact terms, physical volume, driving frequency normalization, or electric-field conversion;
- generic Transport must not acquire model-specific assumptions from `Transport.Models`.

`QuantumTheory.LinearResponse.FiniteLehmannTable` evaluates each transition through the canonical
scalar owner `Lehmann.Transition`, independently of operator spectral reconstruction.
`Lehmann.Eigenbasis.Data` owns the Hilbert-basis data; `Lehmann.Eigenbasis.Table` adapts it to the
finite scalar table. Operator-derived response endpoints consume the transition record's
`frequencyTerm` directly rather than assembling its energy gap and weight separately.
`EnergyEigenbasisLehmannData` supplies a complete orthonormal energy eigenbasis and normalized
diagonal state probabilities. The `Eigenbasis` module and function names describe this supplied
representation; neither finiteness of the spectral index nor a pure state is assumed by that name.
The table evaluates each transition through the canonical
`finiteLehmannTableTransitionData` record. Its `.weight`, `.energyGap`, and frequency evaluation
belong to that transition data; concrete validation and conductivity adapters consume those fields.
The diagonal-weight vanishing theorem remains a canonical simplification rule, independently of
any response or physical conductivity prefactor.

`QuantumTheory.Occupation.Band` owns arbitrary occupation-law composition with band energies, while
`QuantumTheory.Occupation.ZeroTemperature` owns the strict scalar Fermi step and its pointwise
properties. Neither requires transport theory.
`QuantumTheory.Occupation.BandFilling` owns zero-temperature occupied regions, Fermi surfaces,
filled/empty/partially-filled band predicates, and their correspondence to the spectral occupation
law. These are independent of response theory. `Analysis.ZeroTemperatureLorentzian` owns the
transport-side finite-window Fermi-edge integrals, arctangent formulas, broadening limits, and
isolated-pole weights.

`Analysis.ContinuumMeasure` owns the opt-in two-dimensional physical-momentum convention
`d²p/(2πℏ)²` and its exact full-angle radial prefactor `2π/(2πℏ)²`; these are continuum conventions,
not dimension-independent transport invariants. `Analysis.AngularHarmonics`
owns the reusable constant/first/second harmonic
coefficient decomposition and ordinary full-angle cancellation laws. `Analysis.PolarFourier`
consumes the same coefficient data for phase-weighted radial-axis reduction while keeping the
zeroth, first-cosine, and second-cosine kernels explicit. Model layers supply coefficient values;
Pauli algebra, propagator data, and radial physics remain model-owned.

## Resolvent and response boundary

`QuantumTheory.LinearResponse.RetardedSusceptibility` owns the commutator and causal kernels,
their stationarity laws, and linearity in the measured observable. It depends on the expectation
and free-dynamics interface rather than perturbative derivation. `ResponseChannel` consumes this
kernel directly. `SourceCoupling` owns the source-coupled Kubo derivative theorem, while
`ObservableVariation` adds the affine measured-observable/contact contribution. Consumers of
channel data or frequency kernels therefore need not import the Dyson/Kubo derivation.

`Resolvent.Basic` owns the signed spectral parameter `z(E, γ) = E + iγ`, `SpectralSide`, and the
physical `E ± iη` specializations. Analytic resolvent theorems are stated at arbitrary `γ` whenever
the argument does not intrinsically depend on retarded/advanced branch semantics. The conversion
from a physical side and broadening to the analytic regulator is owned by
`SpectralSide.regulator`; physical consumers should use `side.regulator η` instead of reconstructing
its `side.sign * η` representation. `spectralParameter` and `spectralResolvent` are the canonical
side-indexed physical owners, while conventional retarded/advanced names are retained as consumed
specializations.

Generic bounded-resolvent facts belong upstream in `Analysis.Operator.Spectral.Resolvent`.
`Resolvent.Spectral` specializes those facts to the arbitrary signed-regulator transport parameter
without importing response data. `Spectral.Eigenbasis` is the neutral adapter that combines this
generic resolvent action with `EnergyEigenbasisLehmannData`; Kubo–Bastin and Středa both consume that
adapter rather than owning duplicate pure-point spectral proofs.

`Resolvent.SelfEnergy` owns the representation-independent two-sided Dyson relation
`IsSelfEnergy G₀ G Σ` and its inverse-difference characterization when compatible inverses are
available.

`KuboBastin` owns the finite/pure-point response algebra built on that spectral adapter. `Streda` owns the static
surface/sea operator and traced response representation, together with the representation-level
`ℏ/(2π)` trace prefactor and its composition with an explicitly supplied continuum-measure
normalization. `Core.ConductivityTensor` is independent of either representation.

## Response limits

Response limit predicates belong to `LinearResponse.Frequency.LimitOrder`, independently of a spectral
realization; finite sums use Mathlib's general filter-limit theorem. `Lehmann.Limits` owns transition-family
nonresonance results; `Lehmann.Eigenbasis.Limits` combines the operator specialization and physical
three-stage limits. Finite-window convergence is owned by `Frequency.InfiniteTime`. Zero switching
rate is evaluation of the same transition `frequencyTerm` at rate zero, not a second scalar value.
Positive-rate regulator removal, two-sided static limits, and observation-time-first order remain
distinct explicit conditions.

## Stationary channel response

For a real-valued external profile, the derivative theorem in `LinearResponse.Response.ObservableVariation`
uses `ResponseChannel.causalResponse` directly. Its `observableVariation` is the actual coefficient
`A₁` in `A₀ + λ A₁`; the channel does not multiply it by the external profile again. A geometric
current with contact operator `C` supplies `A₁ = f(t) C`. At observation time the normalized cosine
profile gives `A₁ = C`, while the sine profile gives `A₁ = 0`, using the generic profile computation
rules in `LinearResponse.Frequency.HarmonicSource`. Current self-adjointness is supplied by the lattice
realization, and no complex-valued Hamiltonian perturbation is introduced.

`ResponseChannel.finiteTimeAdiabaticResponse_eq_stationaryLag` owns the stationary change from
source time to nonnegative lag, including the stationary observable-variation expectation.
`ResponseChannel.infiniteTimeAdiabaticResponse` denotes the half-line lag transform plus that
contact expectation. Its observation-time convergence is proved in `LinearResponse.Frequency.InfiniteTime`,
either from explicit lag integrability or from a positive switching rate for bounded operators.
The observation-time source value is factored out; real harmonic quadratures retain their own
source-dependent contact factors.

`Fermionic.Transport.ChargeCurrentChannel` supplies `boundedDirectionalResponseChannel`: measured and source operators
are the directional current, and observable variation is the Peierls contact operator. Spectral
response and finite-volume conductivity consume the channel directly. Frequency, switching-rate,
and volume limits remain distinct, and the finite stationary lag identity requires nonnegative
observation time.

The charge-current channel module imports the channel and free-system interfaces directly; it
performs no frequency transform or time integration. `Fermionic.Transport.CorrectedCurrentResponse`
owns both `boundedFluxRetardedResponse` and its corrected-current representation laws. The intrinsic
flux is realized as a bounded observable before applying the measured-linear retarded kernel;
representation laws only identify it on exact differentials, not arbitrary global currents.

## Static response identification

`Streda.StaticChannelIdentification` owns the conditional identification of a complete static
channel response with the traced Bastin integral. `StaticChannelTracedBastinIdentity` is an explicit
assumption equating the vertex response to `V (-η)` times the traced integral minus the
observable-variation expectation. It does not prove a model-specific Ward identity. Measured and
source operators remain independent; the complete response includes the observable variation
before the static electric-field normalization is cancelled. This differs from the vertex-only
representation consumed by `Streda.GeneralizedStatic`. Nonzero switching rate suffices for
normalization cancellation; the spectral integral identification requires positive switching rate.

`Fermionic.Transport.FiniteDisorderConductivity` averages the spectral conductivity at zero driving
frequency and applies the generic conditional identification separately in each configuration.
It keeps the averaged conductivity as the physical endpoint rather than introducing a second
configuration-conductivity interface.

## Disorder boundary

```text
Finite ──→ Resolvent ──→ AveragedSelfEnergy
  │            │
  └──→ Moments ├──→ Born
               ├──→ Ladder
               └──→ SCBA
```

`Disorder.Finite` owns the normalized finite ensemble. `Disorder.Resolvent` owns exact clean,
configuration, and averaged Green operators at arbitrary signed regulator `γ`. Exact configuration
Dyson expansions are owned at arbitrary nonzero `γ`; physical consumers specialize the regulator
locally when branch semantics are required.

`FiniteDisorderEnsemble.average` is a complex linear map given by the normalized weighted finite
sum. The ensemble-independent connected two-point subtraction belongs to
`QuantumTheory.LinearResponse.connectedCorrelation`. Its definition requires only a
functional and ordered multiplication of observables, not Gibbs, KMS, or Gaussianity.
For a normalized expectation it is the physical second cumulant; normalization makes
identity insertions vanish.
`Disorder.ConnectedCorrelation` takes a supplied normalized expectation for each configuration
and averages that connected correlation **after** evaluating each configuration's expectation.
The disconnected product remains inside the average; its difference from the product of
separately averaged one-point functions is the disorder covariance. A four-leg expansion
must be supplied explicitly.
The module needs neither a Fock-space realization nor spectral data or a conductivity definition;
an eigenbasis density state can be supplied by a physical consumer.

`Disorder.Moments` owns the exact second-moment action `C₂(X) = E[Vω X Vω]` and centered-disorder
data.

`Disorder.AveragedSelfEnergy` is exact: at arbitrary nonzero `γ` it proves invertibility of the exact
averaged Green operator on an arbitrary complete complex Hilbert space and defines
`exactSelfEnergyOfRegulator = G₀⁻¹ - Ḡ⁻¹`, satisfying `IsSelfEnergy`.

`Disorder.Born` owns `bornSelfEnergyOfRegulator`, the conventional first-Born self-energy obtained by
applying the exact second-moment action to the clean Green operator at arbitrary `γ`.

`Disorder.SCBA` records supplied self-consistent approximation data and derives its side-indexed
consequences. Here retarded/advanced branch semantics are part of the physical approximation data,
so SCBA remains explicitly `SpectralSide`-aware rather than being treated as an analytic regulator
wrapper. `Disorder.Ladder` owns the RA kernel for supplied Green operators and the generic
fixed-point/resummation algebra for bounded complex-linear endomorphisms. Conditional resummation
and uniqueness use the canonical `IsUnit (1 - L)` hypothesis on the space where the ladder is
represented; no geometric-series convergence is assumed. Concrete invariant subspaces, such as the
massive-Dirac in-plane Pauli coefficient space, may therefore use the same resummation theorem after
proving their restricted shift is a unit. The disorder layer does not expose separate inverse-data,
one-rung, or residual routing APIs and does not assume a Ward identity.

## Scalar-impurity T-matrix ownership

MassiveDirac.Disorder.TMatrix.ScalarImpurity owns the scalar-impurity parameters, unit-guarded
T-matrix and self-energy algebra, operator-norm bounds, and the quadratic small-strength remainder
for an explicitly supplied 2×2 Green loop. It depends on the model's matrix/operator realization,
without importing continuum measures or real-space propagators.

TMatrix.BornDysonLoop owns the finite-cutoff Born-Dyson loop at the spatial origin, its zero-disorder
clean-loop identity, and the Born self-energy coefficient under W = n_imp v_imp². The physical
momentum measure is attached by the loop realization exactly once; the mean-potential term remains
separate. TMatrix is the package entry point for these two responsibilities.
## Concrete models

The `Models.RashbaExchange` family owns its clean Rashba-exchange Hamiltonian and spectral
identities in `Model`, `Model/Spectral`, and `Model/Interband`. The finite-response bundle
and momentum disk live in `ResponseParameters`. The clean bounded Hamiltonian and velocity are defined in `Operator`; their band-projector
spectral identities are in `Model/OperatorSpectral`. The signed charge and bounded current
vertices, including ordered projector-current traces, live in `Current`; retarded/advanced
resolvents are in `Green`. Berry/force-matrix bridges and finite Bastin/Středa response stay
in model-owned downstream modules. Generic trace, measure, and conductivity constructions remain upstream
under `Transport`.

`Models.Parabolic2DEG` is the public route for the finite isotropic parabolic-band
normalization benchmark. It keeps effective mass, chemical potential, radial cutoff, positive
spectral broadening, signed charge/current convention, reduced Planck constant, and momentum-measure
normalization explicit. `Model` owns only the clean Hamiltonian and velocity;
`ResponseParameters` owns the finite-response parameter bundle and cutoff domain;
`Green` owns finite-broadening scalar/operator resolvents; and `Response` owns
charge-current vertices together with the finite conductivity calculation. The pointwise response consumes the
common finite-broadening Středa surface kernel `RA - (RR + AA)/2` through these operators. The reduced
finite-cutoff response remains a response-level object until the named `ℏ/(2π)` Kubo trace
prefactor is attached; only then is it exposed through `Core.ConductivityTensor`. No thermodynamic,
cutoff-removal, or zero-broadening limit is part of this benchmark.

`Models.MassiveDirac` is the public route for the massive-Dirac transport benchmark.
Its explicit clean Pauli Green operator and continuum Born self-energy follow the same split as the
generic disorder layer: arbitrary-regulator definitions/theorems own the analytic calculation, while
side-indexed objects are retained only at reusable physical boundaries such as broadening limits,
Born-Dyson dressing, and RA vertex calculations. Physical-side specializations consume the canonical
`SpectralSide.regulator` conversion rather than depending on the sign representation directly.

The current-rung, ladder determinant, solved-vector, dressed-current, and momentum-integral
fixed-cutoff metallic Born-Dyson zero-broadening boundaries share one explicit
`FixedCutoffMetallicBornRegime` domain package. It owns only the common velocity, mass, probe-energy,
disorder, reduced-Planck, cutoff, metallic-shell, and cutoff-orientation data. Conductivity charge
normalization, real Born-renormalization bounds, and ladder determinant nonvanishing remain explicit
at the result boundaries that consume them; the regime package is not a replacement for the scaling
domain or for generic denominator APIs.

The Hall and longitudinal Středa radial integrals use the shared integration law for
`inPlaneLadderAction` from `Vertex.InPlaneLadder`. Their fixed-disorder zero-broadening proofs use
the existing full-vector convergence law for the same action. The ordered Hall sign and the
longitudinal bare RR/AA remainder remain with their respective response constructions.

`Disorder.FiniteBroadeningBornRadialMoments` owns the finite-cutoff Born–Dyson single-pole
logarithmic integral, the arbitrary-weight retarded–advanced double-pole spectral difference,
and its logarithmic specialization. These are model-level denominator identities independent
of a particular response channel. The Gaussian-crossed K0/K2 current harmonics
consume the common owner directly, rather than importing the longitudinal same-side
Středa remainder merely to obtain a radial logarithmic primitive. The RR/AA
same-side remainder stays in its own response-specific module.

`Disorder.FiniteBroadeningCurrentVertexResponse` owns the source-indexed dressed current,
its source evaluations, and its fixed-disorder zero-broadening insertion. Continuity of the
in-plane rotation and current realization belongs to `Vertex.InPlaneLadder` and `Model.Operator`.
Středa trace adapters consume these results; the same-side remainder and conductivity normalization
remain separate.

`Disorder.FiniteBroadeningCurrentVertexZeroBroadeningIntegral` owns the common radial
factorization of the zero-broadening current-rung entries. The weak-disorder Lorentzian reduction
and the scaled transverse limit consume that identity, while keeping their distinct limit arguments
and assumptions local.

The massive-Dirac continuum normalization keeps each physical factor at the narrowest owner.
`Analysis.ContinuumMeasure` owns both the bare physical-momentum measure and its exact full-angle
radial prefactor. `Disorder.ContinuumMeasurePrefactor` owns one external scalar-disorder line times
one bare physical-momentum measure independently of where angular reduction is performed, while
`Streda.ConductivityNormalization` owns the model-independent Bastin/Středa trace prefactor and its
composition with continuum normalization. Momentum-space non-crossing
responses consume the physical-momentum conductivity normalization only after their response
integral is formed. Real-space crossed Fourier blocks already contain their physical momentum
measures upstream, so a later crossed conductivity boundary must consume only the remaining
trace/current normalization rather than attach another momentum measure.

`MassiveDirac.Streda.GaussianCrossedRealSpaceIntegral` owns the pointwise antisymmetric
radial trace reductions for both crossed topologies, including their explicit K0/K1/K2
moment expressions. Intermediate harmonic reductions are private proof stages. The
`Conductivity.Hall.GaussianCrossed` module integrates those trace identities and attaches
the physical current and trace prefactors. Ordered radial kernels remain distinct from
the antisymmetric trace used for Hall conductivity.

`Analysis.InternalSpace.Pauli` owns coefficient extraction through entrywise interval
integrals with a complex prefactor. These laws use Mathlib's integral addition,
subtraction, division, and constant-multiplication results; no additional linear-map
representation is needed. `Disorder.FiniteBroadeningBornRadialRealSpacePropagator`
owns the radial Green coefficient integration laws, while
`Streda.GaussianCrossedRadialCoefficients` owns the crossed-current laws. Both consume
the same model-independent Pauli integration laws with explicit entrywise integrability.

Concrete models may consume generic Transport and Analysis results, but reusable mathematics or
transport infrastructure should be moved upstream rather than duplicated in a concrete model.
Massive-Dirac Bastin band, pole, and Berry calculations consume the ordered
`Model.OperatorSpectral.currentBandBlockTrace` directly. The finite band-sum expansion
normalizes its current-first trace order locally using finite trace cyclicity; it does
not expose a second trace representation to downstream consumers.
The canonical top-level owner of all three concrete benchmark families is `Models`;
`Transport` contains only reusable model-independent theory.

## Import boundaries

- generic Transport must not import `LeanCondensedMatter.SecondQuantization`;
- generic `Transport` modules must not import concrete `Models` modules;
- model-specific code must not define generic Transport APIs solely for one concrete consumer.
