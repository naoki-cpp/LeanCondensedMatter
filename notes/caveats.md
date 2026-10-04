# Caveats

Active mathematical and formalization constraints. Remove an entry when the limitation no longer
applies.

## Quantum and operator analysis

- **The real spectral trace is not the general trace API.**
  `ContinuousLinearMap.SpectralTraceClass` is the self-adjoint specialization of general trace-class
  membership; compactness and absolute spectral summability are derived. `spectralTrace` is the real
  eigenvalue sum with multiplicity. The canonical trace on general trace-class bounded operators is
  `IsTraceClass.trace : ℂ`, and on the self-adjoint specialization it agrees with `spectralTrace`
  after coercion to `ℂ`.

- **Hilbert-basis diagonal operators are not trace-class-specific.**
  `Analysis/Operator/Diagonal.lean` constructs the absolutely summable rank-one series and proves
  its basis action and compactness. Positivity and spectral-trace packaging are separate adapters
  under `Analysis/Operator/TraceClass/`.

- **The general trace-class API is not yet complete as a normed operator ideal.**
  `ContinuousLinearMap.IsTraceClass T` is implemented through Hilbert–Schmidt membership of
  `sqrt(|T|)`, with a basis-independent real trace norm and basis-independent complex trace. Every
  trace-class operator is compact. Membership is closed under addition, scalar multiplication,
  adjoint, and bounded left/right multiplication. The trace norm is invariant under adjoint and nonincreasing under multiplication
  by contractions, with the general bounds `‖WT‖₁ ≤ ‖W‖ ‖T‖₁` and
  `‖TW‖₁ ≤ ‖W‖ ‖T‖₁`. The canonical complex trace is cyclic under bounded
  left/right multiplication; completeness remains missing.

- **Fredholm determinant support is diagonal, not general.**
  `Analysis/Operator/Fredholm/Diagonal.lean` provides a genuinely infinite-dimensional determinant
  for explicit absolutely summable diagonal coefficients `coeff i`, using the convergent product
  `∏' i, (1 + coeff i)`. This does not define a determinant for arbitrary compact, normal, or
  trace-class operators. Reindexing invariance is proved, but independence from an unrelated
  diagonalizing basis needs a separate spectral-uniqueness theorem.

- **`ContinuousLinearMap.det` is not an infinite-dimensional Fredholm determinant.**
  Mathlib's determinant is used only for finite-dimensional compatibility. It must not be applied
  through fallback behavior or weakened hypotheses to define the infinite-dimensional quantity.
  The general Fredholm theory still requires trace-class approximation/completeness and a
  convergent presentation-independent determinant construction.

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

- **`QuantumTheory.StateVector` stores a unit-vector representative, not a physical state.**
  Physical pure states are represented by the density-backed subtype `QuantumTheory.PureState`; two
  normalized representatives define the same physical pure state exactly when they differ by a
  unit-modulus global phase. A separate projective/ray quotient presentation is not implemented.

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
