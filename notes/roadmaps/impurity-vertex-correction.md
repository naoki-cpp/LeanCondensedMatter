# Conserving impurity vertex-correction boundary

In the current SCBA/non-crossing ladder scheme, a conserving impurity construction uses the same
disorder second moment in the one-particle self-energy approximation and the two-particle ladder
vertex. This note records the current bounded boundary and the missing conservation bridge.

## Shared disorder data

`Transport.Disorder.Moments` owns the exact finite-ensemble second-moment action

```text
C₂(X) = E[Vω X Vω].
```

For self-adjoint impurity potentials and real ensemble weights, its adjoint compatibility is proved.
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
finite fixed-point iteration, and a corrected vertex represented by `(I - L_RA)⁻¹ J` only when the
required inverse is supplied. The corresponding fixed-point equation and uniqueness are proved under
that hypothesis. One-rung aliases and residual-routing declarations are not separate public APIs.
No geometric-series convergence or Ward identity is inferred from the ladder algebra alone.

## Conservation target

For a bounded conserved charge vertex `Q`, the intended conserving bridge requires explicit symmetry
assumptions such as

```text
H₀ Q = Q H₀
Vω Q = Q Vω
```

or an equivalent equivariance statement for `C₂`, together with SCBA and ladder data built from the
same second-moment action. The target is a finite retarded-advanced Ward-consistency theorem relating
the SCBA resolvent difference to the corresponding corrected charge vertex.

This is weaker than a full electromagnetic Ward--Takahashi identity.

## Open work

- prove the finite charge-vertex Ward-consistency bridge under explicit symmetry hypotheses;
- connect a corrected vertex to Kubo--Bastin/Středa conductivity with source, contact, and tensor
  normalization assumptions stated explicitly;
- justify SCBA or ladder convergence under useful analytic hypotheses;
- crossed diagrams, weak localization, skew scattering, and side-jump decompositions;
- trace-per-unit-volume, thermodynamic, DC, and zero-broadening limits;
- infinite-dimensional nonlinear SCBA fixed-point analysis.
