---
status: accepted
---

# Separate algebraic Fock constructions from analytic realizations

Keep occupation-space algebra, basis-independent fermionic algebra, and Hilbert-space completion as distinct representations. Common's algebraic Fock space is the finitely supported vector space `Config →₀ ℂ`; fermionic `AlgebraicFock` is the exterior algebra of the one-particle space; completed occupation space is an ℓ² space.

The exterior algebra supports basis-independent creation and contraction, while occupation coordinates support explicit operator calculations. Relate these through proved maps and equivalences after supplying the appropriate basis. Algebraic identities alone do not establish boundedness, domain closure, or convergence on a completion.

For finite configurations, retain both the continuous-operator realization on `Config → ℂ` used by operator integration and the Hilbert realization on `EuclideanSpace ℂ Config` used by adjoints and density expectations. The extra bridges preserve the structures needed by each consumer instead of treating finite-dimensional representations as definitionally interchangeable.

Evidence: [occupation algebra](../../LeanCondensedMatter/SecondQuantization/Common/Algebra/AlgebraicFock.lean), [exterior algebra](../../LeanCondensedMatter/SecondQuantization/Fermionic/Algebra/AlgebraicFock/Basic.lean), [completion](../../LeanCondensedMatter/SecondQuantization/Fermionic/CompletedSpace/Basic.lean), [finite analytic realization](../../LeanCondensedMatter/SecondQuantization/Common/Perturbation/FiniteAnalyticBridge.lean), and [finite Hilbert realization](../../LeanCondensedMatter/SecondQuantization/Common/Algebra/FiniteHilbertOperator.lean).
