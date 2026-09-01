# Caveats

Active mathematical and formalization constraints. Remove an entry when the limitation no longer
applies.

## Quantum and operator analysis

- **The project’s spectral trace is not a general trace-class ideal.**
  `ContinuousLinearMap.SpectralTraceClass` is built for compact self-adjoint operators and defines
  trace through real eigenvalues with multiplicity. It does not provide a trace on every
  non-self-adjoint trace-class operator, a full Schatten hierarchy, or all ideal/product closure
  theorems.

- **The Hilbert–Schmidt API does not yet supply a general trace-class product ideal.**
  The project proves basis independence, adjoint invariance, bounded-composition closure, and the
  Hilbert–Schmidt pairing. It has not yet bundled arbitrary products of two Hilbert–Schmidt
  operators as non-self-adjoint trace-class operators carrying a general trace.

- **Fredholm determinant support is diagonal, not general.**
  `Analysis/Operator/Fredholm/Diagonal.lean` provides a genuinely infinite-dimensional determinant
  for explicit absolutely summable diagonal coefficients `coeff i`, using the convergent product
  `∏' i, (1 + coeff i)`. This does not define a determinant for arbitrary compact, normal, or
  trace-class operators. Reindexing invariance is proved, but independence from an unrelated
  diagonalizing basis needs a separate spectral-uniqueness theorem.

- **`ContinuousLinearMap.det` is not an infinite-dimensional Fredholm determinant.**
  Mathlib's determinant is used only for finite-dimensional compatibility. It must not be applied
  through fallback behavior or weakened hypotheses to define the infinite-dimensional quantity.
  The general Fredholm theory still requires a non-self-adjoint trace-class ideal, convergence, and
  determinant identities on the valid domain.

- **Density-state expectations are more general than the available spectral trace of a product.**
  For a density operator `ρ` and bounded operator `A`, the product `ρ.op ∘L A` need not be
  self-adjoint. `DensityOperator.expectation` is therefore defined from `ρ`’s spectral decomposition.
  In finite dimensions it is proved equal to the ordinary matrix trace `Tr(ρA)`.

- **A bounded Hamiltonian does not yield a genuine infinite-dimensional compact Gibbs operator.**
  `gibbsOp Hop β = exp (-β Hop)` is invertible. If it is compact, the identity is compact and the
  Hilbert space is finite-dimensional. Infinite-dimensional Gibbs states require an unbounded
  Hamiltonian or semigroup theory with domains.

- **Von Neumann entropy may be infinite.** A trace-one positive operator can have a summable
  eigenvalue sequence while `∑ -λ log λ` diverges. The canonical entropy is therefore `ENNReal`-
  valued. Use `.toReal` only after proving the entropy is not `⊤`.

- **`Real.log 0 = 0` is a total-function convention.** Arguments involving relative entropy or
  logarithms of density eigenvalues must state the required strict-positivity or support hypotheses.
  Do not reason as though Lean automatically supplies the extended-real value `-∞`.

- **Continuous functional calculus instances may need to be enabled locally.** Consumers using
  `cfc` on bounded operators may require
  `attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus` together with the
  appropriate Mathlib imports.

- **Avoid reindexing dependent spectral index Sigma types when a sum can be split.**
  `EigenvectorIndex T` has finite-dimensional fibers depending on the eigenvalue. When the summand
  is independent of the fiber coordinate, use `Summable.tsum_sigma` and evaluate the finite inner
  sum rather than constructing casts and `HEq` proofs between dependent index types.

## State and measurement models

- **`QuantumTheory.State` stores a unit-vector representative.** The quotient by global phase is not
  implemented. The proved phase-invariance theorems justify representative-independent expectation
  values but do not make the state type definitionally a projective Hilbert space.

- **POVMs are countable and discrete.** The current `QuantumTheory.POVM` does not model continuous
  outcomes, measurable operator-valued measures, or instruments/state update.

## Second quantization

- **Algebraic Fock space is not a completed Hilbert space.** Coordinate identities on
  `AlgebraicFock` do not automatically establish boundedness, closability, self-adjointness, or
  domain properties on completed Fock space.

- **Bosonic occupation space is infinite even for finitely many modes.**
  `Bosonic.Occupation Mode := Mode →₀ ℕ` is not a finite type. Finite-configuration trace arguments
  cannot be reused without summability proofs.

- **Bosonic creation, annihilation, and number operators are unbounded in the completed theory.**
  They must not be represented as bounded continuous linear maps unless the chosen restriction or
  cutoff makes boundedness true and that fact is proved.

- **Thermal pairing formulas require a free or quasifree state.** An arbitrary interacting Gibbs
  state does not satisfy a pairings-only Bloch–de Dominicis expansion.

## Combinatorics

- **Formal linked-cluster identities do not imply analytic convergence.** Coefficientwise cumulant
  and connected-diagram theorems are valid independently of convergence of the perturbation series,
  existence of `log Z` outside a formal neighborhood, or a thermodynamic limit.
