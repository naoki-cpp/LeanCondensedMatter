# Transport ownership

The transport stack is organized by mathematical ownership rather than by the first concrete
consumer.

```text
QuantumTheory.LinearResponse
          ↓
QuantumTheory.Transport
  finite Kubo–Bastin / Středa / resolvents / disorder
      ↙                                  ↘
SecondQuantization.Fermionic.Transport   concrete statistics-neutral models
  finite-Fock, lattice, directional-     e.g. Transport.AnomalousHall
  current, occupation specializations
      ↓
fermionic / lattice model consumers
```

Concrete model modules may consume the neutral `Transport` layer directly when no fermionic
realization is required. They must not become owners of reusable Kubo–Bastin, Středa, resolvent, or
disorder machinery.

## Public umbrella boundary

`LeanCondensedMatter.Transport` is the public umbrella for generic transport infrastructure only. It
must not re-export concrete benchmark umbrellas such as `LeanCondensedMatter.Transport.AnomalousHall`.
The project root `LeanCondensedMatter.lean` imports the generic transport umbrella and concrete AHE
umbrella explicitly as separate public tracks, so the all-inclusive root remains all-inclusive without
collapsing the ownership boundary.

Implementation modules should continue to import the narrow transport leaves they actually use rather
than depending on either umbrella.

## Generic transport boundary

Files under `LeanCondensedMatter/Transport/` are statistics-neutral transport theory and statistics-
neutral concrete consumers. They must not import `LeanCondensedMatter.SecondQuantization`.

Reusable generic transport declarations belong in neutral owner modules outside concrete model
subtrees. The canonical generic owners include:

- `FiniteTrace` for the ordinary finite-dimensional operator trace, cyclicity, and differentiation
  through that trace;
- `Resolvent` for dimension-independent retarded/advanced Green operators and their algebraic
  identities;
- `ResolventSpectral` for the action of those resolvents on arbitrary Hamiltonian eigenvectors and
  the derived pure-point basis formulas;
- `FiniteKuboBastin` for finite measured/source Kubo–Bastin response;
- `StredaOccupation`, `StredaCommonKernel`, and `GeneralizedStaticStreda` for the regularized Středa
  chain;
- `FiniteDisorder` for exact finite ensembles and exact scalar/operator averages;
- `FiniteDisorderResolvent` for exact clean/configuration Green operators and configuration-wise
  Dyson identities;
- `FiniteDisorderBorn` and `FiniteDisorderAdvancedBorn` for first-Born approximation boundaries and
  explicit closure errors;
- `FiniteDisorderSCBA` for supplied self-consistent Born data and Ward-consistency identities.

`FiniteKuboBastin` consumes `ResolventSpectral` for the transition-energy specialization of the
retarded eigenvector formula rather than reproving inverse-operator algebra. `StredaTraceSpectral`
consumes the same owner for arbitrary-energy retarded/advanced pure-point factors. The old
Středa-named resolvent-spectral owner is retired because the underlying theorem is not Středa-specific.

`StredaTraceKernel` consumes `FiniteTrace` to turn Středa operator kernels into scalar trace kernels.
`FiniteDisorder` also consumes `FiniteTrace` directly when proving that exact finite averaging commutes
with the ordinary trace; exact disorder must not depend on the Středa trace layer solely for this
generic operation.

Finite dimensionality belongs only at theorem boundaries that actually require an ordinary trace or
a finite spectral sum.

## Fermionic transport boundary

`SecondQuantization/Fermionic/Transport` owns genuinely fermionic or lattice realizations: finite
Fock carriers, directional charge current, Peierls contact terms, Fermi occupation/state data, and
finite-volume conductivity specializations.

A fermionic module may wrap a generic theorem when the wrapper names a real physical specialization,
but it should import and specialize the canonical neutral owner rather than re-prove or re-own the
statistics-independent theorem.

In particular:

```text
KuboBastinSpectral  → Transport.FiniteKuboBastin
StredaOccupation    → Transport.StredaOccupation
StredaCommonKernel  → Transport.StredaCommonKernel
StaticKuboBastinResponse → Transport.GeneralizedStaticStreda
```

## Disorder boundary

The exact/approximate split is intentionally explicit:

```text
FiniteDisorder
  exact ensemble + exact averages
        ↓
FiniteDisorderResolvent
  exact Gᴿ/Gᴬ + exact configuration Dyson identities
        ↓
FiniteDisorderBorn / FiniteDisorderAdvancedBorn
  moments + averaged remainder + Born approximation + closure error
```

SCBA is not a child of the first-Born closure layer:

```text
FiniteDisorder + Resolvent
        ↓
FiniteDisorderSCBA
```

`FiniteDisorderMomentData` and `FiniteCovarianceSuperoperator` are deliberately separate. The former
stores centered exact second-moment data used by first Born; the latter is a bounded complex-linear,
adjoint-compatible covariance superoperator used by SCBA. Do not merge them merely for naming
symmetry.

Model-specific scalar disorder, Pauli decompositions, scattering rates, NCA vertices, and crossed
diagrams belong downstream and must preserve the distinction between exact finite averages and
weak-disorder approximations.
