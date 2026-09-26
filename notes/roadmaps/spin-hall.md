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
This file supplies the spin-Hall specialization and links those generic tasks
to concrete model and observable choices. Issue #1159 remains the owner of the
generic current/source architecture; this roadmap owns the spin-Hall model
specializations.

## Phased roadmap

### R0 -- provenance and terminology (documented)

* Keep the referent table for every new name before opening a PR.
* Add primary citations for the intrinsic, vertex, proper-current, and skew
  claims to `notes/references.md`.
* Mark Kato, Kimura, Ando, and related device papers as validation boundaries,
  not as proofs of a finite Lean response.

### R1 -- finite Rashba response (next implementation slice)

Define a bounded finite two-dimensional spinful lattice or momentum-grid model
with an explicit Rashba term, charge-driving source, velocity, and spin-space component vector. Prove the finite mixed Kubo response is well-typed and state the
symmetry assumptions needed for a transverse component. Keep broadening,
volume, and charge/sign conventions as named parameters.

Acceptance criteria:

1. the model instantiates the existing arbitrary-polarization `SpinCurrentResponse` API;
2. the conventional spin current is visibly `1/2 {v, S(n)}` for the selected spin component;
3. no claim of a universal infinite-system value is made without an order of
   limits and a non-degeneracy/broadening hypothesis.

### R2 -- clean intrinsic benchmark

Specialize R1 to the clean/interband regime discussed by Sinova et al. and
prove a finite spectral identity for the chosen response kernel. Only after
that identity is stable should a continuum or universal-value bridge be
considered. The bridge must state which bands are occupied, whether both
Rashba branches are present, and how the zero-broadening limit is taken.

### R3 -- disorder vertices and cancellation

Use the existing finite second-moment and retarded-advanced ladder layers to
encode an impurity covariance and response vertex. Reproduce the isotropic
short-range cancellation benchmark from Inoue et al. under explicit finite
assumptions, then add a forward-scattering counterexample. The result should
separate the bare current, the ladder-dressed vertex, and the resummation
hypothesis; it should not assert convergence of an uncontrolled physical
approximation.

### R4 -- proper-current specialization

Specialize the abstract corrected-current layer to a spin-orbit model and prove
when the correction is the torque-dipole term of Shi et al. Record separately
the symmetrized (conventional) current, the proper current, and any effective observable
used by a contact calculation. The theorem must expose the localization and
boundary assumptions rather than treating an exact commutator identity as a
universal physical equivalence.

### R5 -- extrinsic mechanisms

Introduce the smallest finite impurity model that can distinguish side-jump
and skew-scattering contributions. Use Dyakonov--Perel as historical
provenance and Niimi et al. as a scale/sign benchmark, while keeping material
parameters and fitted spin Hall angles outside the core. Add mechanism labels
only when the decomposition is invariant under the declared convention.

### R6 -- inverse response and reciprocity

Add a spin-source/charge-observable response and formulate an Onsager-type
reciprocity theorem with time-reversal, magnetization, and source conventions
visible. Kimura et al. is the experimental benchmark. Link the implementation
to the source-dependent observable/contact work tracked by issue #1159.

### R7 -- bulk, edge, and validation boundary

Only after the finite model is stable, pursue trace-per-volume and controlled
thermodynamic/DC limits, edge accumulation, spin diffusion, interface mixing,
and experimental normalizations. Kerr rotation, inverse-SHE voltage, ST-FMR,
spin Hall magnetoresistance, and spin Hall-angle extraction belong here as
validation or separate applied-model issues, not as prerequisites for the
finite algebraic theorems.

## Priority and issue split

* **P0:** R1 finite Rashba model and R4 proper-current specialization.
* **P1:** R2 clean intrinsic identity and R3 ladder cancellation.
* **P2:** R5 extrinsic mechanism benchmark and R6 inverse reciprocity.
* **P3:** R7 bulk/edge/device validation and material-specific calibration.

The implementation work should be tracked as a separate roadmap issue rather
than mixed into the documentation PR. The documentation PR carries citations,
semantic boundaries, and this roadmap; the issue carries the R1--R7 acceptance
criteria and dependency order.

## References

See the annotated entries in [`../references.md`](../references.md) for full
citations, DOI links, and caveats. In particular, primary theory provenance is
Dyakonov--Perel (1971), Sinova et al. (2004), Inoue et al. (2004), and Shi et
al. (2006); Niimi et al. (2012) is the extrinsic benchmark. Kato et al. (2004),
Kimura et al. (2007), and Ando--Saitoh (2012) are explicitly experimental
validation references.
