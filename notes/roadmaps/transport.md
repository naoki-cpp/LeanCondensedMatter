# Transport roadmap

This track separates four questions that must not be conflated:

1. whether the Hilbert space is finite- or infinite-dimensional;
2. whether the physical system has finite volume or is treated in an infinite-volume limit;
3. whether the response uses an ordinary finite trace, a trace-class expression, or a trace per unit volume;
4. whether a displayed conductivity formula has been derived from time-dependent linear response or merely adopted as a convention.

The reusable transport data should be as general as the bounded-operator infrastructure permits. More
restrictive assumptions belong on the individual response theorems that need them.

## Required logical chain

The transport program does not take Kubo–Bastin as its foundational definition. The intended theorem
chain is

```text
time-dependent perturbation
  → interaction-picture propagator / Duhamel–Dyson expansion
  → first variation of an observable expectation
  → causal retarded commutator kernel (Kubo formula)
  → explicit electrical source and measured-current model
  → frequency-domain regularized conductivity
  → finite spectral/Kubo–Greenwood form
  → Kubo–Bastin resolvent representation
  → Středa surface/sea decomposition.
```

Every arrow should be implemented by a theorem or guarded by explicit analytic hypotheses. In
particular, writing down the Bastin trace expression is not itself a derivation of the Kubo formula.

The issue graph is

```text
#365 bounded transport conventions and dimensional boundary
  ├─> #443 causal Kubo formula from time-dependent perturbations
  │      └─> #444 electrical-conductivity specialization and contact term
  └─> #366 dimension-independent retarded/advanced resolvent identities

#444 + #366
  └─> #367 finite-dimensional Kubo–Bastin derivation
         └─> #368 regularized Středa decomposition
                └─> #369 finite toy-model validation
                       └─> #370 finite disorder averaging
                              └─> #371 Born self-energy
                                     └─> #372 vertex-correction design.
```

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

Issue #365 fixes data and conventions only. It does not prove the Kubo formula, identify an external
electric-field coupling, or define the Bastin expression as a foundational conductivity law.

## Causal linear response — issue #443

The missing foundation is the Kubo theorem itself. Start with a bounded perturbation

```text
H_λ(t) = H₀ - λ f(t) B
```

and a stationary unperturbed expectation. The interaction-picture propagator should be obtained from a
Duhamel/Volterra equation or Dyson expansion. Differentiating the perturbed expectation at `λ = 0`
should yield, with the sign fixed by the coupling above,

```text
d/dλ ⟨A(t)⟩_λ |₀
  = (i/ℏ) ∫_{t₀}^{t} f(s) ⟨[A_I(t), B_I(s)]⟩₀ ds
  = -(i/ℏ) ∫_{t₀}^{t} f(s) ⟨[B_I(s), A_I(t)]⟩₀ ds.
```

The integration domain supplies causality. Under stationarity, the two-time kernel should reduce to a
function of `t - s`. Frequency-domain and Lehmann corollaries require separate integrability,
switching, and finite-dimensional hypotheses.

This result is general quantum linear response and should live under `QuantumTheory.LinearResponse` or
a comparably general layer. General Dyson/Volterra facts currently owned by SecondQuantization may need
to be extracted to `Analysis`; `QuantumTheory` must not import `SecondQuantization`.

## Electrical-conductivity specialization — issue #444

A general Kubo commutator is not yet an electrical conductivity theorem. The external source and the
measured current must be modeled explicitly.

Two first-slice routes are possible:

1. couple an electric field to a bounded polarization/dipole observable and study the response of
   `Jα`; or
2. use a differentiable vector-potential family `H(A)` and define
   `Jα(A) = -∂H(A)/∂Aα`.

The second route generally produces both the state-response commutator and an explicit derivative of
the current observable with respect to the source, often called the contact or diamagnetic term. It
must not be silently omitted. The first route avoids a source-dependent current but has position,
periodic-boundary, and boundedness limitations.

Issue #444 chooses one bounded finite-volume vertical slice, derives the conductivity kernel from
#443, fixes Fourier and source conventions, and derives the finite spectral/Kubo–Greenwood expression
that #367 will consume.

Driving frequency `ω`, switching rate, resolvent broadening `η`, observation-time limits, and the
`ω → 0` or `η → 0` limits are distinct quantities until a theorem identifies them. Their order of
limits must be explicit.

## Retarded and advanced convention — issue #366

For real energy `E`,

```text
zᴿ(E, η) = E + iη,
zᴬ(E, η) = E - iη,
Gᴿ(E, η) = (zᴿ(E, η) I - H)⁻¹,
Gᴬ(E, η) = (zᴬ(E, η) I - H)⁻¹.
```

For bounded self-adjoint `H`, invertibility at `η > 0`, the identity `Gᴬ = (Gᴿ)†`, the resolvent
identity, and the energy-derivative identity are dimension-independent statements. Issue #366 should
prove them on arbitrary Hilbert spaces where the available Mathlib inverse API permits, rather than
adding finite-dimensionality by default.

This resolvent branch can proceed in parallel with the Kubo-response branch after #365. Resolvent
algebra alone does not produce a conductivity theorem.

## Kubo–Bastin derivation — issue #367

For a finite-volume system, the intended regularized representation is of the form

```text
σᵝᵃ_η(μ)
  = -(ℏ / (2π V)) ∫_{-∞}^{μ} dE Tr[
      Jα (∂E Gᴿ) Jβ (Gᴿ - Gᴬ)
      - Jα (Gᴿ - Gᴬ) Jβ (∂E Gᴬ)
    ].
```

This expression is a target representation, not the definition of linear response. Issue #367 must
prove it equal to the finite spectral/Kubo–Greenwood conductivity obtained in #444, using the
resolvent identities from #366.

No additional factor of `q²` is inserted when `Jα` already contains the charge. A model formulated
with charge-independent velocity operators must first set `Jα = q vα`; the resulting expression then
contains the expected quadratic charge dependence. If the current depends on the external source, the
contact term derived in #444 must either be retained or shown to cancel/combine under explicit
hypotheses.

The first exact implementation may use a finite-dimensional specialization because the ordinary trace
and arbitrary non-self-adjoint operator products are immediately available there. That restriction
belongs on the Kubo–Bastin theorem, not on `BoundedSystem`, the Kubo theorem, or the resolvent algebra.

An infinite-dimensional version needs explicit hypotheses ensuring that the relevant products are
trace-class and that trace cyclicity is valid. The repository's current spectral trace-class API does
not yet constitute a general non-self-adjoint trace ideal, so this extension must not be claimed merely
by removing a typeclass assumption.

## Infinite-volume boundary

An infinite-volume conductivity is not obtained by setting `V = ∞` or omitting the volume field. It
normally requires a trace per unit volume, a covariant/ergodic operator framework, or a controlled
thermodynamic limit of finite-volume responses. Those constructions are a later program and must be
stated with their topology, normalization, and convergence assumptions.

Thus the broader intended sequence is

```text
arbitrary-Hilbert bounded Kubo and resolvent identities
  → finite-dimensional or trace-class finite-volume conductivity
  → Bastin and Středa representations in the same trace regime
  → trace-class and/or trace-per-unit-volume extensions
  → thermodynamic, DC, and zero-broadening limits.
```

## Středa decomposition target

Issue #368 will define a Fermi-surface term `σᴵ` and a Fermi-sea term `σᴵᴵ` using the same
`Gᴿ/Gᴬ`, current, volume, source, contact-term, and `ℏ` conventions, and prove

```text
σ_η = σᴵ_η + σᴵᴵ_η.
```

The first proof may inherit the finite-dimensional or trace-class hypotheses of #367. At this stage
`σᴵᴵ` is only the Fermi-sea contribution to the response; it is not identified with a magnetic
derivative of density or magnetization.

## Explicit deferrals

The following are outside the first slices:

- finite-temperature Fermi–Dirac response;
- unbounded Hamiltonians, polarization/position operators, and domain-sensitive current constructions;
- full equivalence of length and velocity gauges;
- disorder ensembles, Born approximations, and vertex corrections before the clean chain is complete;
- a general non-self-adjoint trace-class ideal;
- trace-per-unit-volume and infinite-volume response;
- thermodynamic, DC, long-time, or zero-broadening limits without explicit convergence theorems;
- magnetic-field derivatives of density or magnetization.

## Sources

- Kubo, *Statistical-Mechanical Theory of Irreversible Processes. II* (1957).
- Bastin et al., *The conductivity tensor of a three-dimensional system in a magnetic field* (1971).
- Smrčka and Středa, *Transport coefficients in strong magnetic fields* (1977).
