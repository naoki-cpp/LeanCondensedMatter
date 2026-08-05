# Roadmap — Basis-independent fermionic fields and conserved current

Issue: #524

## Representation decision

The foundational one-particle space is an arbitrary complex vector space and later an arbitrary
complex Hilbert space. It is not assumed finite-dimensional.

The basis-independent algebraic finite-particle Fock space is represented by

```text
ExteriorAlgebra ℂ 𝓗₁.
```

Its homogeneous `n`-particle sector is the mathlib submodule

```text
⋀[ℂ]^n 𝓗₁.
```

This choice gives a canonical wedge product and a canonical one-particle embedding without choosing
an orthonormal basis. It also keeps every algebraic Fock vector finite-particle, so creation,
contraction, and second-quantized operator identities can be proved before introducing completed
Hilbert direct sums or unbounded-operator domains.

## Separation from the occupation representation

The existing

```text
Fermionic.FockSpace Mode
```

is the free complex vector space on finite subsets of an ordered mode type. It is well suited to
explicit mode calculations, finite traces, Wick expansions, and the current finite-mode LCT.

The new

```text
Fermionic.Field.FiniteParticleFock 𝓗₁
```

is basis-independent and accepts arbitrary one-particle vectors directly. Neither representation is
a compatibility alias for the other. Their comparison requires a chosen basis and a theorem that
identifies wedge basis states with signed occupation states.

No existing occupation-space API is replaced in the first field-theory slices.

## Analytic boundary

`ExteriorAlgebra ℂ 𝓗₁` is an algebraic finite-particle space, not the completed Hilbert Fock space.
Even when a one-particle operator `T` is bounded, its full second quantization `dΓ(T)` is generally
unbounded across all particle-number sectors. The field line therefore separates:

1. algebraic identities on finite-particle Fock space;
2. completed Hilbert-space and domain theory, introduced only when required;
3. bounded bridges to Kubo response, such as fixed-particle sectors or explicit cutoffs.

## Planned slices

1. **F1 — foundation:** exterior-algebra Fock space, vacuum, sectors, and one-particle embedding.
2. **F2 — smeared fields:** exterior multiplication, inner-product contraction, and smeared CAR.
3. **F3 — second quantization:** `dΓ(T)` and its commutator identities.
4. **F4 — weak continuity:** smeared charge density and the Schrödinger continuity equation.
5. **F5 — lattice current:** discrete continuity and the hopping/bond-current formula.
6. **F6 — gauge equivalence:** agreement with the Peierls link derivative.
7. **F7 — bounded response bridge:** transport the derived current into #443 and #444.

## First-slice acceptance

- the one-particle space has no finite-dimensionality or basis assumption;
- the Fock object is basis-independent;
- vacuum and homogeneous particle sectors are exposed;
- the one-particle embedding is proved injective;
- the occupation and exterior representations remain explicitly distinct;
- the full public `SecondQuantization` import exposes the new field umbrella.
