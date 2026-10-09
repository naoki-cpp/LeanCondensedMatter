---
status: accepted
---

# Prefer intrinsic mathematical structures over case-specific representations

When several physics-facing constructions differ only by an algebraic sign, an
index choice, a coordinate basis, or a representation, express the shared law
using its intrinsic mathematical structure. Derive individual physical cases
as specializations or through proved representation bridges instead of
maintaining parallel theorem families.

Examples already embodied in the repository include:

- The exchange sign `Statistics.zetaInt` and generic exchange bracket unify
  fixed-statistics CAR/CCR rearrangements without identifying the fermionic
  and bosonic Fock representations.
- Linear maps and operators keep mathematical identities independent of a
  chosen vector basis or matrix-coordinate expansion.
- Statistics-independent pairing combinatorics and connected-decomposition
  identities live upstream of physics-specific diagram signs and amplitudes.
- Periodic Bloch projector families use Mathlib's `IsStarProjection` rather
  than reintroducing self-adjointness and idempotence as model-specific fields.

This decision concerns **which mathematical object owns an identity**,
rather than where to place its file; module ownership remains governed by
[ADR 0002](0002-semantic-ownership.md).

Introduce a new public abstraction only if the shared object is mathematically
meaningful and at least one concrete theorem or consumer becomes simpler.
Prefer a canonical Mathlib structure or an existing project API. Use an
explicit `structure` or a theorem when data or assumptions are noncanonical;
a `class` is appropriate only when instance inference expresses a stable
mathematical choice. Do not create a generalization whose only effect is to
wrap an already generic theorem.

Abstraction must preserve distinctions that affect the truth of the result:
bosonic and fermionic occupation representations, graded versus ungraded
operators, ordering signs, source-coupling conventions, operator domains,
summability, spectral gaps, and convergence conditions. A generic algebraic
identity does not establish the analytic properties of its concrete
realization.

This rule trades a modest upstream abstraction and explicit specialization
bridges for fewer duplicated proofs and clearer mathematical invariants. It
also constrains abstraction: if two representations have different semantics
or no actual common consumer, retain them as separate canonical APIs.

Evidence: [statistics and exchange algebra](../../LeanCondensedMatter/SecondQuantization/Common/Algebra/ExchangeAlgebra.lean),
[generic exchange sign](../../LeanCondensedMatter/Combinatorics/ExchangeSign.lean),
[pairing weights](../../LeanCondensedMatter/SecondQuantization/Common/Thermal/BlochDeDominicis/PairingWeight.lean),
[connected decomposition](../../LeanCondensedMatter/Combinatorics/Cumulant/ConnectedDecomposition.lean),
[periodic Bloch projector](../../LeanCondensedMatter/Transport/Topology.lean),
and [refactoring conventions](../conventions.md).

Potential future generalizations are tracked separately in the
[unifying-structures roadmap](../roadmaps/unifying-structures.md);
the candidates listed there are not accepted architectural decisions.
