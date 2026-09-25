# Conserving impurity vertex-correction boundary

In the current SCBA/non-crossing ladder scheme, a conserving impurity construction uses the same
disorder second moment in the one-particle self-energy approximation and the two-particle ladder
vertex. This note records the current bounded boundary and the finite conservation bridge.

## Shared disorder data

`Transport.Disorder.Moments` owns the exact finite-ensemble second-moment action

```text
C₂(X) = E[Vω X Vω].
```

For self-adjoint impurity potentials and real ensemble weights, its adjoint compatibility is proved.
When every impurity potential commutes with a bounded operator `Q`, the second moment is also
equivariant on both sides, so `C₂(X) Q = C₂(X Q)` and `Q C₂(X) = C₂(Q X)`.
`C₂` is exact ensemble data; Born, SCBA, and ladder constructions that consume it are approximation
layers unless separately identified with exact averages.

## SCBA boundary

`Transport.Disorder.SCBA` records supplied retarded SCBA fixed-point and inverse data and derives the
advanced side by adjoint. Algebraic consequences such as the matching second-moment difference
relation are exact once those data are supplied.

The module does not prove existence, uniqueness, or convergence of the nonlinear SCBA fixed point,
and does not identify an SCBA Green operator with the exact disorder-averaged Green operator.

## Ladder boundary

`Transport.Disorder.Ladder` owns the retarded-advanced action

```text
L_RA(Γ) = C₂(Gᴿ Γ Gᴬ).
```

It keeps the reusable algebra at the level actually needed downstream: the supplied-Green RA kernel,
finite fixed-point iteration, and a corrected vertex represented by `(I - L_RA)⁻¹ J` under the
canonical `IsUnit (1 - L_RA)` hypothesis. The corresponding fixed-point equation, uniqueness, and
complex linearity in the bare vertex are proved under that hypothesis. Separate inverse-data,
one-rung, and residual-routing declarations are not public APIs. No geometric-series convergence or
Ward identity is inferred from the ladder algebra alone.

## Conservation bridge

`Transport.Disorder.Ward` packages the minimal bounded charge-symmetry data used by the proof:

```text
H₀ Q = Q H₀,
C₂(X) Q = C₂(X Q),
Q C₂(X) = C₂(Q X).
```

For a finite ensemble, pointwise impurity commutation `Vω Q = Q Vω` is proved sufficient to
construct this interface; it is not required as part of the public Ward assumption.

Combining that equivariance with the supplied SCBA inverse relations and the generic
retarded-advanced ladder gives, under `IsUnit (1 - L_RA)`,

```text
Γ_Q = (I - L_RA)⁻¹ Q,
(zᴬ - zᴿ) • (Ḡᴿ Γ_Q Ḡᴬ) = Ḡᴿ Q - Q Ḡᴬ.
```

Thus the Ward theorem uses the generic corrected charge vertex with bare vertex `Q` directly.
The proof reuses generic ladder fixed-point uniqueness; there is no SCBA-specific ladder
resummation API. This finite bounded identity is weaker than a full electromagnetic
Ward--Takahashi identity.

## Open work
- connect a corrected vertex to Kubo--Bastin/Středa conductivity with source, contact, and tensor
  normalization assumptions stated explicitly;
- justify SCBA or ladder convergence under useful analytic hypotheses;
- crossed diagrams, weak localization, skew scattering, and side-jump decompositions;
- trace-per-unit-volume, thermodynamic, DC, and zero-broadening limits;
- infinite-dimensional nonlinear SCBA fixed-point analysis.
