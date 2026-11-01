---
status: accepted
---

# Separate algebraic Fock constructions from analytic realizations

When `OccupationBasis` supplies per-mode occupations and finite support, define total particle number once in `SecondQuantization.Common` for arbitrary mode types, without `[Fintype Mode]` and without unifying fermionic and bosonic configuration types. Fermionic cardinality and bosonic finitely-supported sums are representation-specific specializations; creation/removal transitions remain in their statistics owners.

Keep occupation-space algebra, basis-independent fermionic algebra, and Hilbert-space completion as distinct representations. Common's algebraic Fock space is the finitely supported vector space `Config →₀ ℂ`; fermionic `AlgebraicFock` is the exterior algebra of the one-particle space; completed occupation space is an ℓ² space.

The exterior algebra supports basis-independent creation and contraction, while occupation coordinates support explicit operator calculations. Relate these through proved maps and equivalences after supplying the appropriate basis. Algebraic identities alone do not establish boundedness, domain closure, or convergence on a completion.

For infinite-mode fermions, use `ℓ²(Finset Mode, ℂ)` with algebraic finite-particle vectors as a dense core. Keep creation and annihilation bounded where the CAR justify it; model genuinely unbounded diagonal Hamiltonians with explicit maximal domains and closed operators, not continuous linear maps. State the topology of finite-mode approximation at each result: strong convergence of coordinate projections, weak convergence of Gibbs states against bounded operators, and no implied trace-norm convergence.

For finite configurations, retain both the continuous-operator realization on `Config → ℂ` used by operator integration and the Hilbert realization on `EuclideanSpace ℂ Config` used by adjoints and density expectations. The extra bridges preserve the structures needed by each consumer instead of treating finite-dimensional representations as definitionally interchangeable.

Use the existing representation equivalences directly rather than operation-specific forwarding
declarations. Keep finite support distinct from a finite configuration type: an algebraic vector has
finite support even over an infinite configuration type. Reachable-support integrals reconstruct
finite output columns without requiring a finite output basis, while agreement with Bochner
integration is a separate bridge through the analytic realization.

Basis-independent fields are smeared creation and annihilation operators. Point fields are
operator-valued distributions and do not belong to the foundational operator interface.

Evidence: [occupation algebra](../../LeanCondensedMatter/SecondQuantization/Common/Algebra/AlgebraicFock.lean), [exterior algebra](../../LeanCondensedMatter/SecondQuantization/Fermionic/Algebra/AlgebraicFock/Basic.lean), [generic completed Fock core](../../LeanCondensedMatter/SecondQuantization/Common/CompletedSpace/Basic.lean), [generic weighted diagonal operators](../../LeanCondensedMatter/SecondQuantization/Common/CompletedSpace/Diagonal.lean), [fermionic completed specialization](../../LeanCondensedMatter/SecondQuantization/Fermionic/CompletedSpace/Basic.lean), [finite analytic realization](../../LeanCondensedMatter/SecondQuantization/Common/Perturbation/FiniteAnalyticBridge.lean), and [finite Hilbert realization](../../LeanCondensedMatter/SecondQuantization/Common/Algebra/FiniteHilbertOperator.lean).
