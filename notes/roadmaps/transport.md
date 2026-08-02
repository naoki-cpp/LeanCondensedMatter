# Transport roadmap

This track separates three questions that must not be conflated:

1. whether the Hilbert space is finite- or infinite-dimensional;
2. whether the physical system has finite volume or is treated in an infinite-volume limit;
3. whether the response uses an ordinary finite trace, a trace-class expression, or a trace per unit volume.

The reusable transport data should be as general as the bounded-operator infrastructure permits. More
restrictive assumptions belong on the individual response theorems that need them.

## First vertical slice — issue #365

The Lean-facing data are defined in `LeanCondensedMatter/Transport/System.lean`.

`QuantumTheory.Transport.BoundedSystem H` is defined on an arbitrary complete complex Hilbert space.
It does **not** assume `[FiniteDimensional ℂ H]`. Its conventions are:

- `H` is a bounded self-adjoint Hamiltonian;
- `Jα` is supplied independently as a bounded self-adjoint physical current observable;
- `q` is the signed carrier charge and is used when a model constructs `Jα = q vα`;
- `ℏ > 0` is stored explicitly rather than set to one;
- `μ` is the zero-temperature Fermi energy;
- `Pμ = 1_{(-∞, μ]}(H)` is supplied as a self-adjoint idempotent commuting with `H`;
- `η > 0` is the broadening.

`QuantumTheory.Transport.FiniteVolumeSystem H` extends this data only by adding a finite volume
`V > 0`. An infinite-dimensional Hilbert space can therefore still be used for a finite-volume model.
Conversely, an infinite-volume or thermodynamic-limit theory requires a different normalization and is
not represented merely by dropping `[FiniteDimensional ℂ H]`.

The Fermi-projector convention includes the equality edge: states at energy exactly `μ` are occupied.
The current API records the projector and its algebraic properties; constructing the discontinuous
spectral projection from a suitable functional calculus is a later theorem.

The Hamiltonian and currents are bounded in this first interface because the repository currently has a
mature bounded continuous-linear-map API. Genuinely unbounded Hamiltonians and current operators require
a separate domain-aware layer.

## Retarded and advanced convention

For real energy `E`,

```text
zᴿ(E, η) = E + iη,
zᴬ(E, η) = E - iη,
Gᴿ(E, η) = (zᴿ(E, η) I - H)⁻¹,
Gᴬ(E, η) = (zᴬ(E, η) I - H)⁻¹.
```

For bounded self-adjoint `H`, invertibility at `η > 0`, the identity `Gᴬ = (Gᴿ)†`, and the resolvent
identity are dimension-independent statements. Issue #366 should prove them on arbitrary Hilbert spaces
where the available Mathlib inverse API permits, rather than adding finite-dimensionality by default.

## Regularized Kubo–Bastin target

For a finite-volume system and `Jα` interpreted as the physical current operator, the first response
target is

```text
σᵝᵃ_η(μ)
  = -(ℏ / (2π V)) ∫_{-∞}^{μ} dE Tr[
      Jα (∂E Gᴿ) Jβ (Gᴿ - Gᴬ)
      - Jα (Gᴿ - Gᴬ) Jβ (∂E Gᴬ)
    ].
```

No additional factor of `q²` is inserted when `Jα` already contains the charge. A model formulated
with charge-independent velocity operators must first set `Jα = q vα`; the resulting expression then
contains the expected quadratic charge dependence.

The first exact implementation in #367 may use a finite-dimensional specialization because the
ordinary trace and arbitrary non-self-adjoint operator products are immediately available there. That
restriction belongs on the Kubo–Bastin theorem, not on `BoundedSystem`.

An infinite-dimensional version needs explicit hypotheses ensuring that the relevant products are
trace-class and that trace cyclicity is valid. The repository's current spectral trace-class API does
not yet constitute a general non-self-adjoint trace ideal, so this extension must not be claimed merely
by removing a typeclass assumption.

## Infinite-volume boundary

An infinite-volume conductivity is not obtained by setting `V = ∞` or omitting the volume field. It
normally requires a trace per unit volume, a covariant/ergodic operator framework, or a controlled
thermodynamic limit of finite-volume responses. Those constructions are a later program and must be
stated with their topology, normalization, and convergence assumptions.

Thus the intended sequence is:

```text
arbitrary-Hilbert bounded resolvent identities
  → finite-dimensional or trace-class finite-volume Bastin formula
  → Středa decomposition in the same trace regime
  → trace-class and/or trace-per-unit-volume extensions
  → thermodynamic and zero-broadening limits
```

## Středa decomposition target

Issue #368 will define a Fermi-surface term `σᴵ` and a Fermi-sea term `σᴵᴵ` using the same
`Gᴿ/Gᴬ`, current, volume, and `ℏ` conventions, and prove

```text
σ_η = σᴵ_η + σᴵᴵ_η.
```

The first proof may inherit the finite-dimensional or trace-class hypotheses of #367. At this stage
`σᴵᴵ` is only the Fermi-sea contribution to the response; it is not identified with a magnetic
derivative of density or magnetization.

## Explicit deferrals

The following are outside the first slice:

- finite-temperature Fermi–Dirac weights;
- unbounded Hamiltonians, position operators, and domain-sensitive current constructions;
- disorder ensembles, Born approximations, and vertex corrections;
- a general non-self-adjoint trace-class ideal;
- trace-per-unit-volume and infinite-volume response;
- thermodynamic or zero-broadening limits;
- magnetic-field derivatives of density or magnetization.

## Sources

- Kubo, *Statistical-Mechanical Theory of Irreversible Processes. II* (1957).
- Bastin et al., *The conductivity tensor of a three-dimensional system in a magnetic field* (1971).
- Smrčka and Středa, *Transport coefficients in strong magnetic fields* (1977).
