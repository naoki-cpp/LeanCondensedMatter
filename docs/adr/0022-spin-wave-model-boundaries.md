# Separate exact spin models, magnon approximations, and macroscopic magnetization

Status: accepted. This records the approved spin-wave architecture; implementation has
not established these interfaces. See the [roadmap](../roadmaps/spin-waves.md) for targets.

Spin-wave physics connects finite quantum spins, bosonic approximations, and classical
magnetization fields. These objects have different state spaces and hypotheses. Preserve
those distinctions and connect them by explicit representation, approximation, or response
comparison theorems. Start with the exact finite spin-1/2 ferromagnetic ring and derive
its one-magnon operator from the full spin Hamiltonian.

## Decision

- Localized-spin models own spin configurations, site operators, exchange and Zeeman
  couplings, and invariant excitation sectors. Reuse the Pauli representation for spin
  1/2. A lattice position paired with an internal spin label is a one-particle space,
  not the many-site localized-spin space.
- General finite-function, permutation, Fourier, and operator mathematics belongs in
  Mathlib or the project's mathematical layer. Model-independent facts needed from a
  fermionic module must be moved to their mathematical owner, not imported into spin
  physics through fermionic transport.
- Bosonic algebra owns Fock operators and CCR. The exact Holstein-Primakoff representation
  is a model bridge with occupation cap 2s; bare creation need not preserve that subspace.
  Do not impose exact canonical bosonic commutators on a finite-dimensional truncated
  oscillator space. Prove the spin algebra for the composite spin operators instead.
- Linear spin-wave theory owns the explicitly truncated quadratic model. Exact results
  about this model are distinct from error bounds relative to the original spin system.
  Reuse free-boson thermal and quartic machinery only under their actual hypotheses.
- Macroscopic magnetization dynamics owns the effective field, damping, linearization,
  and constitutive susceptibility. It may start independently of a microscopic derivation.
  Polder and Kubo susceptibilities are identified only by a theorem fixing their physical
  observables, source conventions, normalization, and approximation assumptions.

Use real physical parameters and explicit hbar, bond counting, field units, and Fourier
sign conventions at model boundaries. The finite ring counts each nearest-neighbor
bond once. Broader lattice models must explain any directed-neighbor convention.

## Trade-offs and alternatives

Defining only a one-magnon hopping operator would reach the dispersion quickly but leave
its relation to a spin system assumed. Starting with a universal arbitrary-spin or
infinite-volume framework would delay an exact benchmark. The finite spin-1/2 ring
provides a tractable full-model derivation; later extensions must justify generalization.

Identifying finite spin states with unrestricted bosons would erase the occupation cap
and change equilibrium properties. Keeping the exact subspace and approximate model
separate adds representation proofs, but exposes the domain where each theorem applies.

A common susceptibility interface alone would hide whether a result came from quantum
response or a phenomenological equation. Separate constructions permit both developments
while reserving their equality for a meaningful physical comparison.

## Consequences

Zero-field degeneracy is retained: a zero-momentum one-magnon state can have zero
excitation energy. An unrestricted zero-energy bosonic mode cannot use the positive-energy
Gibbs construction without an additional constraint or regulator. Thermodynamic limits,
spontaneous order, approximation-error estimates, and material predictions remain distinct
theorems, not consequences of finite-mode algebra.

This extends the ownership rules of [ADR 0002](0002-semantic-ownership.md), the Fock
boundary of [ADR 0005](0005-fock-representations.md), and the convergence boundary of
[ADR 0007](0007-bosonic-summability-domains.md). The physical source is Stancil and
Prabhakar, *Spin Waves: Theory and Applications* (2009),
[DOI](https://doi.org/10.1007/978-0-387-77865-5), Sections 2.5, 2.7, 3.7-3.8, and 5.1-5.2.
