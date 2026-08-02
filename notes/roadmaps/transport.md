# Finite-system transport roadmap

This track starts with a clean, finite-dimensional, finite-volume response problem. It does not
silently stand for an infinite crystal or a thermodynamic limit.

## First vertical slice — issue #365

The Lean-facing data are defined in
`LeanCondensedMatter/Transport/FiniteSystem.lean` as
`QuantumTheory.Transport.FiniteSystem`.

The conventions are:

- `H` is a bounded self-adjoint Hamiltonian on a finite-dimensional complex Hilbert space;
- `Jα` is supplied independently as a bounded self-adjoint physical current observable;
- `V > 0` is the finite sample volume;
- `q` is the signed carrier charge and is used when a model constructs `Jα = q vα`;
- `ℏ > 0` is stored explicitly rather than set to one;
- `μ` is the zero-temperature Fermi energy;
- `Pμ = 1_{(-∞, μ]}(H)` is supplied as a self-adjoint idempotent commuting with `H`;
- `η > 0` is the finite broadening.

The Fermi-projector convention includes the equality edge: states at energy exactly `μ` are occupied.
The current API records the projector and its algebraic properties; construction by spectral or
continuous functional calculus is a later theorem. This is a finite-system spectral projector, not a
thermodynamic-limit Fermi sea.

## Retarded and advanced convention

For real energy `E`,

```text
zᴿ(E, η) = E + iη,
zᴬ(E, η) = E - iη,
Gᴿ(E, η) = (zᴿ(E, η) I - H)⁻¹,
Gᴬ(E, η) = (zᴬ(E, η) I - H)⁻¹.
```

Thus `Gᴬ = (Gᴿ)†` for self-adjoint `H`; proving invertibility, the adjoint identity, and resolvent
identities is the scope of #366.

## Regularized Kubo–Bastin target

With `Jα` interpreted as the physical current operator, the first response target is

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

The exact finite-dimensional trace expression and its finite spectral/Lehmann form are the scope of
#367. The integral notation above fixes the sign and normalization target; it is not yet a Lean
definition.

## Středa decomposition target

Issue #368 will define a Fermi-surface term `σᴵ` and a Fermi-sea term `σᴵᴵ` using the same
`Gᴿ/Gᴬ`, current, volume, and `ℏ` conventions, and prove

```text
σ_η = σᴵ_η + σᴵᴵ_η.
```

The split is to be obtained from the regularized Bastin expression by finite-dimensional resolvent
identities and integration by parts. At this stage `σᴵᴵ` is only the Fermi-sea contribution to the
response; it is not identified with a magnetic derivative of density or magnetization.

## Explicit deferrals

The following are outside the first slice:

- finite-temperature Fermi–Dirac weights;
- position operators and derivation of current from commutators;
- disorder ensembles, Born approximations, and vertex corrections;
- infinite-dimensional resolvents;
- thermodynamic or zero-broadening limits;
- magnetic-field derivatives of density or magnetization.

## Sources

- Kubo, *Statistical-Mechanical Theory of Irreversible Processes. II* (1957).
- Bastin et al., *The conductivity tensor of a three-dimensional system in a magnetic field* (1971).
- Smrčka and Středa, *Transport coefficients in strong magnetic fields* (1977).
