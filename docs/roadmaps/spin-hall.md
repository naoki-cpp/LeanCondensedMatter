# Spin Hall response roadmap

This roadmap isolates the spin Hall effect (SHE) from the generic transport
infrastructure. It records which papers are evidence for a definition or a
mechanism, which papers are only experimental validation, and which statements
are realistic Lean targets.

## Scope and semantic boundaries

The direct SHE is a transverse spin response to a charge-driving source. The
inverse SHE is the reciprocal conversion from a spin-driving source to a
transverse charge response. The roadmap keeps the following observables
distinct:

* a bulk mixed response (the object already exposed by
  `SecondQuantization/Fermionic/Transport/SpinCurrentResponse.lean`);
* boundary spin accumulation, which requires a finite sample, boundary
  conditions, and a spin-relaxation model; and
* a device-level spin Hall angle, which additionally depends on units,
  geometry, interfaces, and a detection convention.

The conventional spin current is `1/2 {v, S}`. In a spin-orbit-coupled model
this is not automatically the measurable transport current. Shi, Zhang, Xiao,
and Niu motivate a torque-dipole completion; the existing abstract
`ConservationLaw.localizationCorrectionCurrentFlux` is therefore only a semantic hook until a model
identification theorem is proved. No roadmap item should silently identify the
conventional, proper, and effective total-angular-momentum currents.

The mechanism vocabulary is also explicit:

* **intrinsic:** clean/interband spin response of a spin-orbit band model;
* **vertex correction:** disorder correction to a response vertex, not a new
  current operator;
* **extrinsic:** impurity-generated side-jump or skew-scattering response.

## Evidence map

| Source | What it contributes | Lean disposition |
|---|---|---|
| Dyakonov--Perel (1971) | Original current-induced spin orientation and spin-orbit-scattering picture | Historical provenance and an eventual impurity/boundary benchmark; not a direct formalization of the experiment |
| Sinova et al. (2004) | Clean Rashba intrinsic spin Hall response | Primary finite-model target after the Hamiltonian and source conventions are fixed |
| Inoue, Bauer--Molenkamp (2004) | Isotropic short-range disorder can cancel the Rashba response through a vertex correction; forward scattering changes the conclusion | A finite ladder/cancellation theorem with all disorder hypotheses stated |
| Shi et al. (2006) | Proper spin-current definition with torque-dipole completion | Primary semantic source for specializing `CorrectedCurrent.lean`; not a blanket equality for every correction |
| Niimi et al. (2012) | Large extrinsic skew-scattering signal in CuBi | Finite impurity-model benchmark; material calibration remains out of scope |
| Kato et al. (2004) | Optical detection of edge spin accumulation | Experimental validation only; requires boundary and detector models |
| Kimura et al. (2007) | Direct/inverse spin Hall conversion and Onsager reciprocity in a device | Reciprocity target after source/contact conventions are explicit; device measurement is not the theorem |
| Ando--Saitoh (2012) | Inverse SHE detection in silicon | Material/device validation only |
| Manchon et al. (2015, 2019) | Review vocabulary for Rashba coupling and spin-orbit conversion/torque | Secondary terminology and triage references; primary papers remain theorem provenance |

The experimental papers are useful for deciding which observable a future
model should expose, but they are not suitable as direct Lean inputs. Kerr
rotation, spin pumping, spin Hall magnetoresistance, interface mixing, and
spin-diffusion fits should remain downstream validation tracks.

## Current code boundary

The repository already provides a finite mixed response from an electric bond
current to a spin current selected by a spin-space component vector `n ∈ ℝ³`, with a
symmetrized spin current built from `1/2 {v, S(n)}`. The spin-1/2 realization is
`S(n) = ℏ (n · σ) / 2`; Pauli axes are representation coordinates rather than polarization data. It deliberately does not claim a conductivity normalization,
a Rashba Hamiltonian, or equality between spin and charge currents. The
single-particle corrected-current layer provides an exact algebraic correction,
and the one-dimensional Schwartz example proves a commuting-localizer special
case. These are foundations, not an existing SHE theorem.

The transport roadmap already lists vertex-corrected Kubo--Bastin/Streda
response, thermodynamic limits, DC limits, and crossed/side-jump/skew work.
This roadmap specifies spin-Hall model and observable choices; the generic
current/source architecture remains in the transport and linear-response layers.

## First finite Rashba momentum-sector benchmark (partial R1)

`Models.RashbaExchange.SpinCurrent` now defines a finite **single-momentum two-level**
spin/charge response channel built from the physical spin-space polarization
`SpinHalf.SpinSpace`, the clean Rashba velocity `velocityOperator`, and the
signed charge-current vertex `currentBoundedOperator`.

The theorem `conventionalSpinCurrentMatrix_z_eq` derives the operator identity
`{v_i, S_z}/2 = (ℏ_spin/2) (p_i/m_eff) σ_z`: the Rashba velocity term
anticommutes with `σ_z`. The `rashbaSpinChargePointChannel_z_origin_retardedKernel`
theorem then proves that the exact causal Kubo kernel vanishes at the
momentum origin for arbitrary normalized expectations and positive `ℏ`.

**Scope:** this supplies a physically nontrivial single-sector selection rule,
not the full finite 2D spinful lattice or momentum-grid mixed Kubo/Lehmann
calculation requested by R1. The point channel uses the fixed-observable
convention (zero explicit contact variation); it does not identify the
conventional current with the proper/torque-dipole current. A nontrivial
transverse response away from the origin, finite grid assembly, source/contact
identification, and R4 localization bridge remain outstanding.

## Open targets

### Finite Rashba response

Define a bounded finite two-dimensional spinful lattice or momentum-grid model
with an explicit Rashba term, charge-driving source, velocity, and spin-space component vector. Prove the finite mixed Kubo response is well-typed and state the
symmetry assumptions needed for a transverse component. Keep broadening,
volume, and charge/sign conventions as named parameters.

Acceptance criteria:

1. the model instantiates the existing arbitrary-spin-component `SpinCurrentResponse` API;
2. the conventional spin current is visibly `1/2 {v, S(n)}` for the selected spin component;
3. no claim of a universal infinite-system value is made without an order of
   limits and a non-degeneracy/broadening hypothesis.

### Clean intrinsic benchmark

Specialize the finite Rashba model to the clean/interband regime discussed by Sinova et al. and
prove a finite spectral identity for the chosen response kernel. Only after
that identity is stable should a continuum or universal-value bridge be
considered. The bridge must state which bands are occupied, whether both
Rashba branches are present, and how the zero-broadening limit is taken.

### Disorder vertices and cancellation

Use the existing finite second-moment and retarded-advanced ladder layers to
encode an impurity covariance and response vertex. Reproduce the isotropic
short-range cancellation benchmark from Inoue et al. under explicit finite
assumptions, then add a forward-scattering counterexample. The result should
separate the bare current, the ladder-dressed vertex, and the resummation
hypothesis; it should not assert convergence of an uncontrolled physical
approximation.

### Proper-current specialization

Specialize the abstract corrected-current layer to a spin-orbit model and prove
when the correction is the torque-dipole term of Shi et al. Record separately
the symmetrized (conventional) current, the proper current, and any effective observable
used by a contact calculation. The theorem must expose the localization and
boundary assumptions rather than treating an exact commutator identity as a
universal physical equivalence.

### Extrinsic mechanisms

Introduce the smallest finite impurity model that can distinguish side-jump
and skew-scattering contributions. Use Dyakonov--Perel as a theoretical reference and Niimi et al. as a scale/sign benchmark, while keeping material
parameters and fitted spin Hall angles outside the core. Add mechanism labels
only when the decomposition is invariant under the declared convention.

### Inverse response and reciprocity

Add a spin-source/charge-observable response and formulate an Onsager-type
reciprocity theorem with time-reversal, magnetization, and source conventions
visible. Kimura et al. is the experimental benchmark. The source-dependent observable/contact term belongs to the generic response layer.

### Bulk, edge, and validation boundary

Only after the finite model is stable, pursue trace-per-volume and controlled
thermodynamic/DC limits, edge accumulation, spin diffusion, interface mixing,
and experimental normalizations. Kerr rotation, inverse-SHE voltage, ST-FMR,
spin Hall magnetoresistance, and spin Hall-angle extraction belong here as
validation or separate applied-model issues, not as prerequisites for the
finite algebraic theorems.

## Priority

Establish finite Rashba response and proper-current semantics first; then address
clean intrinsic identities and disorder vertices. Extrinsic mechanisms, inverse
reciprocity, and bulk/device limits require additional model-specific hypotheses.

## Finite momentum-grid full-Fock construction (partial R1)

`Models.RashbaExchange.FiniteMomentumSpinResponse` embeds momentum-resolved Rashba
2×2 Hamiltonian and velocity blocks in the one-particle space on a **finite momentum
grid with two spin modes per sampled momentum**, then constructs the finite fermionic
Fock Hamiltonian **directly** via `boundedOneBodyOperator`, without a
fictitious real-space hopping adapter. The shared finite-Fock
`Lattice.isSelfAdjoint_sum_boundedDgammaMatrixUnit_blocks` proves self-adjointness
for arbitrary Hermitian internal matrix blocks and is consumed by
`boundedFiniteMomentumBlockOneBody_selfAdjoint` and
`finiteRashbaMomentumFockHamiltonian_selfAdjoint`. The related
`Lattice.isSelfAdjoint_sum_boundedDgammaMatrixUnit` also replaces the
older, repeated proof in `Validation.TwoSiteOrbitalResponse`.
Its mixed response channel consumes the existing
`Fermionic.Transport.boundedSpinCurrentLinear` API and a signed charge
velocity source `dΓ(q v_j)`. An observable-variation/contact operator is an
explicit input rather than implicitly set to zero. The finite-grid retarded Kubo
kernel is evaluated directly with the existing `ResponseChannel.retardedKernel`
and `freePropagatorGroup` APIs. Spin-polarization linearity follows from the
existing `boundedSpinCurrentLinear` and
`retardedSusceptibilityMeasuredLinearMap`; redundant model-local wrappers were
deleted instead of introducing duplicate theorems.

This is a momentum-grid (not real-space) realization, so the electric source is
the momentum-velocity vertex rather than a fictitious inter-spin Peierls
bond. Free dynamics now uses the proved self-adjointness of the
assembled full-Fock Hamiltonian, with only positive `ℏ` required. A concrete
stationary state, its physical
Lehmann transition data, a verified *nonzero* transverse spin response, and an
identified source/contact variation are still needed to complete R1.
The proper-current/torque-dipole equivalence is deliberately left to R4.

## Spin displacement and torque-dipole specialization (partial R4)

`Models.RashbaExchange.SpinDisplacementBridge` reuses
`ConservationLaw.lie_localizedQuantity` and
`SingleParticle.heisenbergTransportFunctional` /
`heisenbergSourceFunctional` instead of defining another generic
proper-current algebra. For the existing finite momentum-grid Rashba
Hamiltonian and physical spin operator `S(n)`, it proves the exact
Heisenberg identity for a **supplied** one-body position-like observable
`X_i`:

```text
δ_H({X_i,S(n)}/2) = {δ_H(X_i),S(n)}/2 + {X_i,δ_H(S(n))}/2.
```

If a position representation also satisfies the *explicit* assumption
`δ_H(X_i) = v_i`, the first term is the existing conventional spin current;
the second term is the torque dipole. The model-specific theorem
`finiteRashbaMomentumSpinDisplacement_fock_decomposition` lifts this identity
to the full finite fermionic Fock space, reusing `boundedSpinCurrentLinear`.
It does not introduce another Kubo stack.

**Important limitation:** a finite set of sampled momenta alone does not
instantiate the physical position operator `iℏ∂_p`, and a finite-dimensional
commutator does not automatically equal the momentum derivative of a band
Hamiltonian. A concrete spatial/position representation, its boundary and
gauge conventions, and the compatibility condition are still open. The
identity is **conditional**, not an unconditional construction of a physical
proper spin Hall conductivity. A local source-free continuity law additionally
requires a justified torque-divergence representation; the generic
`ConservationLaw.localizationCorrectionCurrentFlux` is a *different*
correction and must not be identified with `{X_i,τ}/2` without proof.

## Conditional spin-displacement Kubo response (partial R4)

`Models.RashbaExchange.SpinDisplacementBridge` also supplies
`finiteRashbaMomentumSpinDisplacementResponseChannel`. It replaces only the
measured observable of the existing finite-grid Rashba spin/charge
`ResponseChannel` by the Fock second quantization of `δ_H({X_i,S(n)}/2)`,
while **preserving the same charge-driving source and supplied contact
observable**.

The model-level
`finiteRashbaMomentumSpinDisplacement_retardedKernel_eq_conventional_add_torque`
applies the established `finiteRashbaMomentumSpinDisplacement_fock_decomposition`
and `retardedSusceptibilityMeasuredLinearMap.map_add`. Conditional on
`δ_H(X_i) = v_i`, it proves the exact finite-Fock *retarded* identity

```text
χᴿ_(dΓ δ_H{X_i,S(n)}/2, dΓ q v_j)
  = χᴿ_(J_conventional, dΓ q v_j)
  + χᴿ_(J_torque-dipole, dΓ q v_j).
```

No independent Kubo machinery or generic response-linearity theorem is
introduced. The result does not include the explicit contact variation
in `ResponseChannel.causalResponse`: the contact for each physical current
must be derived from its own source dependence before a full-response
decomposition is claimed. A finite momentum-grid position realization
and local torque-divergence/boundary conditions also remain unresolved.

## Finite momentum-block position obstruction (partial R4)

`Models.RashbaExchange.VelocityPositionObstruction` records a concrete
limitation of the pointwise momentum-grid construction. For either direction
the clean Rashba 2×2 velocity vertex has

```text
Tr(v_i(p)) = 2 p_i / m_eff.
```

By the existing finite-matrix trace cyclicity,
`Tr((i/ℏ)[H(p),X_i(p)]) = 0` for **every** pointwise 2×2 matrix
`X_i(p)`. Consequently, whenever `p_i/m_eff ≠ 0`,
`no_pointwise_rashba_position_of_nonzero_parabolic_velocity` proves
that no such matrix can realize the Rashba velocity via a Heisenberg
commutator. The no-go holds without any Hermiticity assumption on `X_i`.

This obstruction concerns **pointwise spin matrices**, not an operator
on a momentum-wavefunction space that differentiates in momentum or
mixes different grid points. It does not exclude a suitable real-space
position operator. It is an explicit reason **not** to discharge
`SpinDisplacementBridge`'s conditional `δ_H(X_i)=v_i` assumption by
inventing a momentum-diagonal localizer. A physical spatial or covariant
momentum-derivative representation (with boundary/gauge conditions) is
still needed before using the R4 Kubo identity as a proper spin Hall
conductivity.

## Finite real-space position and hopping commutator (partial R4)

Rather than introduce a second lattice geometry or assume a momentum-block
position, the existing `Analysis.DiscreteLattice` module provides
`LatticeGeometry.directionalPosition`. It uses the physical site coordinates
and the existing site projectors,

```text
X_i = Σ_x r_i(x) |x><x|.
[H,X_i]_{xy} = (r_i(y) - r_i(x)) H_{xy}.
```

The latter identity is proved by
`LatticeGeometry.lie_directionalPosition_latticeKet` for any finite
`LocallyFiniteHopping` model and direction. This fixes the algebraic
real-space velocity as `(i/ℏ)[H,X_i]` with the same oriented displacement
used by geometric bond currents. It does not assert equality with the
momentum-derivative velocity of the previously sampled clean Rashba model.
A concrete Hermitian Rashba hopping discretization, connection to the
existing geometric Peierls current, and the spin-displacement/contact
response specialization remain subsequent tasks. No new generic current
framework or new source convention is introduced.

## Geometric bond current equals the position-derived current (partial R4)

The existing `Analysis.DiscreteLattice` and
`Fermionic.Lattice.GeometricCurrent` now connect the finite position
commutator to the already-defined geometric Peierls current, rather than
introducing another velocity/current implementation.

`LatticeGeometry.lie_directionalPosition_eq_bondSum` uses local continuity,
finite support and orientation reversal to identify

```text
[H,X_i] = (1/2) Σ_xy (r_i(y) - r_i(x)) bondOperator(x,y).
```

`boundedDirectionalCurrent_eq_positionCommutator` lifts this equality by
the existing `boundedOneBodyOperator` and bond-current bridge. In the
existing Peierls convention, with real physical parameters, it reads
`J_i = q dΓ((i/ℏ)[H,X_i])`. No equality with the sampled momentum
derivative is assumed. This is a general finite real-space hopping
identity, independent of particle spin and translation symmetry.

A concrete spinful Rashba hopping model and the spin-displacement /
torque-dipole response based on its real-space position still remain
separate milestones. Contact terms retain the existing Peierls convention.

## Open-boundary real-space Rashba hopping (partial R4)

`Models.RashbaExchange.RealSpaceHopping` constructs a rectangular square
lattice of two spin modes per site using the existing `SpinfulSite` and
`LatticeGeometry`. With spacing `a`, `t=ℏ²/(2m_eff a²)`,
`λ=ℏ α_R/(2a)`, the target-forward hopping blocks are
`T_x=-t I-iλσ_y`, `T_y=-t I+iλσ_x`, with reverse adjoints and
onsite `4t I+Δσ_z`. Natural-coordinate adjacency enforces open boundaries.
The forward-table-plus-adjoint construction gives
`realSpaceRashbaHopping_hasHermitianAmplitudes`, and the shared
`isSelfAdjoint_boundedHoppingHamiltonian` yields
`realSpaceRashbaHamiltonian_isSelfAdjoint` on full finite Fock space.

The generic `LocallyFiniteHopping.ofFiniteAmplitudes` constructs incident
sets from actual nonzero amplitude support, not a fictitious complete
hopping graph. The position and charge current can now consume the same
real-space geometry and Hamiltonian through
`LatticeGeometry.directionalPosition` and
`boundedDirectionalCurrent_eq_positionCommutator`. The signs use
`exp(i p·r/ℏ)`; no Fourier or continuum-limit theorem is asserted.
The real-space spin-displacement, torque-dipole and physical contact
response remain downstream. Algebraic Hermiticity does not require
positive mass, spacing or ℏ; physical applications do.

## References

See the annotated entries in [`../references.md`](../references.md) for full
citations, DOI links, and caveats. In particular, primary theory provenance is
Dyakonov--Perel (1971), Sinova et al. (2004), Inoue et al. (2004), and Shi et
al. (2006); Niimi et al. (2012) is the extrinsic benchmark. Kato et al. (2004),
Kimura et al. (2007), and Ando--Saitoh (2012) are explicitly experimental
validation references.
