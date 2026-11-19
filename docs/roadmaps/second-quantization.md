# Second Quantization roadmap

Second quantization is the many-body, thermal, perturbative, and diagrammatic layer under
`LeanCondensedMatter/SecondQuantization/`.

See also:

- [`second-quantization-status.md`](second-quantization-status.md) for current ownership and proved endpoints;
- [`linked-cluster-theorem.md`](linked-cluster-theorem.md) for connected-diagram results;
- [`completed-space-and-infinite-mode.md`](completed-space-and-infinite-mode.md) for completed-space boundaries.

## Mathematical scope

The algebraic foundations use finite-support occupation states over arbitrary mode types.
A finite-mode assumption is introduced where a theorem enumerates configurations or performs
finite-dimensional trace/operator integration or finite diagram sums. The shared total-number
grade is owned by `Common.OccupationBasis`, with statistics-specific realizations.

Canonical layer direction and import rules are documented in the
[architecture](../architecture/second-quantization.md); proved status is summarized in
[current status](second-quantization-status.md).

## Fermionic line

Fermionic CAR/Fock and free Gibbs/KMS machinery supports the finite-temperature
Bloch–de Dominicis theorem. The finite-mode diagrammatic line proves formal and analytic
log-partition linked-cluster identities and the normalized two-point series identity;
the physical higher-point/source-insertion theorem remains open.

The theorem statements and exact hypotheses belong to the
[linked-cluster roadmap](linked-cluster-theorem.md). Completed free-fermion fields,
explicit diagonal operator domains, and the summability-controlled Gibbs/KMS theory
are covered by the [completed-space boundary](completed-space-and-infinite-mode.md).

## Diagrammatics assumptions

Connected formal power-series identities require normalized moments and
component factorization. Concrete fermionic amplitudes supply the statistics-dependent
sign and pairing data; the generic connected-decomposition machinery does not
imply a source-functional higher-point identity. See the
[linked-cluster boundary](linked-cluster-theorem.md#statistics-independent-moment-boundary).

## Completed fermionic line

Bounded completed creation/annihilation fields, CAR, domain-aware diagonal generators,
and summable free Gibbs/KMS results are proved. Interacting completed-space Dyson
theory and thermodynamic limits remain open; see the
[completed-space boundary](completed-space-and-infinite-mode.md).

## Bosonic line

A finite bosonic mode type still has infinitely many occupation configurations.
Algebraic CCR and convergence-aware free thermal states therefore retain explicit
summability assumptions. The completed representation has self-adjoint free number
and Hamiltonian operators, closed mutually adjoint ladder operators on their
weighted domains, and finite quartic interactions on a dense common domain.

For finite modes with positive effective gaps, every fixed-order quartic Dyson
coefficient is Gibbs-summable and its **formal** logarithm has a connected-diagram
expansion. This does not establish an analytic interacting partition function.
Remaining tasks include explicit mixed-mode/quartic weighted-domain formulas,
interacting-Hamiltonian control, and all-order Dyson convergence. See the
[completed-space boundary](completed-space-and-infinite-mode.md#completed-bosonic-free-thermal-representation)
and [linked-cluster roadmap](linked-cluster-theorem.md#statistics-independent-moment-boundary).

## Research directions

- pre-normalized time-ordered insertions, higher Green functions, and source derivatives;
- bosonic interacting Dyson convergence and analytic linked-cluster theory;
- explicit bosonic mixed-mode/quartic weighted domains and interacting-Hamiltonian control;
- interacting completed-space fermionic perturbation theory;
- infinite-mode and thermodynamic limits under explicit topological and uniform-estimate hypotheses;
- low-order examples only where they clarify the general theorem rather than create wrapper APIs.
