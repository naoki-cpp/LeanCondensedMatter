# Roadmap — Basis-independent fermionic fields and conserved current

Issue: #524

## Representation decision

The foundational one-particle space is an arbitrary complex vector space and later, when contraction
and analytic structure are needed, an arbitrary complex Hilbert space. It is not assumed
finite-dimensional.

The basis-independent algebraic finite-particle Fock space is represented by

```text
ExteriorAlgebra ℂ 𝓗₁.
```

Its homogeneous `n`-particle sector is

```text
⋀[ℂ]^n 𝓗₁.
```

This choice provides a canonical wedge product and one-particle embedding without choosing a basis.
Every algebraic Fock vector has finite exterior degree support, so creation, contraction, and
second-quantized operator identities can be developed before introducing a completed Hilbert direct
sum or domains for unbounded operators.

## Separation from the occupation representation

The existing

```text
Fermionic.FockSpace Mode
```

is the free complex vector space on finite subsets of an ordered mode type. It is suited to explicit
mode calculations, finite traces, Wick expansions, and the current finite-mode linked-cluster line.

The new

```text
Fermionic.BasisIndependent.FiniteParticleFock 𝓗₁
```

accepts arbitrary one-particle vectors directly and does not choose a mode basis. Neither
representation is a compatibility alias for the other. Comparing them requires a chosen basis and a
theorem identifying wedge-basis states with signed occupation states.

No existing occupation-space API is replaced by the first field-theory slices.

## Analytic boundary

`ExteriorAlgebra ℂ 𝓗₁` is an algebraic finite-particle space, not the completed Hilbert Fock space.
Even when a one-particle operator `T` is bounded, its full second quantization `dΓ(T)` is generally
unbounded across all particle-number sectors. The implementation therefore separates:

1. algebraic identities on finite-particle Fock space;
2. completed Hilbert-space and domain theory, introduced only when required;
3. bounded bridges to Kubo response, such as fixed-particle sectors or explicit cutoffs.

## Planned slices

1. **F1 — foundation:** exterior-algebra Fock space, vacuum, sectors, and injective one-particle
   embedding.
2. **F2 — smeared fields:** exterior multiplication, inner-product contraction, and smeared CAR.
3. **F3 — second quantization:** `dΓ(T)` and its commutator identities.
4. **F4 — weak continuity:** smeared charge density and the Schrödinger continuity equation.
5. **F5 — lattice current:** discrete continuity and the hopping/bond-current formula.
6. **F6 — gauge equivalence:** agreement with the Peierls link derivative.
7. **F7 — bounded response bridge:** transport the derived current into #443 and #444.

## F1 acceptance boundary

- the one-particle space has no finite-dimensionality or basis assumption;
- the Fock object is basis-independent;
- vacuum and homogeneous particle sectors are exposed;
- the one-particle embedding is proved injective;
- the vacuum is proved nonzero;
- the occupation and exterior representations remain explicitly distinct;
- the construction is exported through `SecondQuantization.Fermionic.Algebra`.
