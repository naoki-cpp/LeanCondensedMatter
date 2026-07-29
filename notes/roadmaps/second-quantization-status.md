# Second Quantization — Current Status

This page is the current-state companion to
[`second-quantization.md`](second-quantization.md), which retains the longer development narrative and
phase history. The focused execution plan for the fermionic Linked Cluster Theorem is
[`linked-cluster-theorem.md`](linked-cluster-theorem.md). The source of truth for each completed claim
is the referenced Lean module and declaration; all files listed below compile without `sorry`.

## Scope and architecture

The finite-mode fermionic line remains the primary path to the finite-temperature Linked Cluster
Theorem. The bosonic line is developed in parallel where the construction is algebraic or finite
combinatorics. The two lines share statistics-independent definitions and proofs through
[`SecondQuantization/Common/`](../../LeanCondensedMatter/SecondQuantization/Common/).

The parity boundary is analytic rather than combinatorial:

- `FermionOccupation Mode := Finset Mode` is finite when `Mode` is finite.
- `Bosonic.Occupation Mode := Mode →₀ ℕ` remains infinite when `Mode` is finite.
- Consequently, finite sums over all fermionic occupation states cannot be copied to the bosonic
  line; bosonic thermal and Dyson constructions need explicit summability or a convergence-aware
  functional interface.

Sources: `Fermionic/Algebra/Occupation.lean`, `Bosonic/Algebra.lean`,
`Common/Thermal/WeightedDiagonalFunctional.lean`, and
`Common/Perturbation/FiniteOperatorIntegral.lean`.

## Public import layouts

The two statistics-specific APIs use parallel umbrellas wherever their mathematics has matching
responsibilities.

| Area | Fermionic import | Bosonic import |
|---|---|---|
| Algebra | `SecondQuantization.Fermionic.Algebra` | `SecondQuantization.Bosonic.Algebra` |
| Imaginary time | `SecondQuantization.Fermionic.ImaginaryTime` | `SecondQuantization.Bosonic.ImaginaryTime` |
| Free thermal theory | `SecondQuantization.Fermionic.Thermal` | `SecondQuantization.Bosonic.Thermal` |
| Quartic diagrammatics | `SecondQuantization.Fermionic.Diagrammatics` | `SecondQuantization.Bosonic.Diagrammatics` |

The fermionic line additionally exports `SecondQuantization.Fermionic.Perturbation`, containing the
formal partition-series logarithm and finite-basis Dyson construction. There is no bosonic umbrella
with the same role yet because the current operator integral and arbitrary Gibbs expectation depend
on the finite fermionic occupation basis.

`SecondQuantization.Fermionic` imports all five fermionic umbrellas, while
`SecondQuantization.Bosonic` imports the four bosonic umbrellas. Smaller implementation modules remain
separate when they express a useful proof or dependency boundary; the layouts are not forced to have
identical file counts.

The physical Fermionic directories match the five umbrella responsibilities. Common follows the same
five-way layout. Bosonic keeps `Foundations/` and `OperatorAlgebra/` as a useful internal split behind
`Bosonic.Algebra`, while its imaginary-time, thermal, and diagrammatic implementations live under the
matching responsibility directories. Statistics-specific Bloch–de Dominicis files are under
`Bosonic/Thermal/BlochDeDominicis/` and `Fermionic/Thermal/BlochDeDominicis/`; the general recursion
remains under `Common/Thermal/BlochDeDominicis/`.

The Common API uses five corresponding responsibility groups:

| Common import | Scope |
|---|---|
| `SecondQuantization.Common.Algebra` | Algebraic Fock infrastructure, statistics, grading, and CAR/CCR interfaces. |
| `SecondQuantization.Common.ImaginaryTime` | Time ordering, diagonal evolution, interaction pictures, and KMS rotation. |
| `SecondQuantization.Common.Thermal` | Normalized functionals, diagonal traces, Gibbs infrastructure, and Bloch–de Dominicis. |
| `SecondQuantization.Common.Perturbation` | Finite-basis coefficientwise operator integration. |
| `SecondQuantization.Common.Diagrammatics` | Label-generic quartic diagrams, component decomposition, component orders, component-shuffle integrands, and the finite-family component-shuffle product identity. |

The extraction decisions, completed thin Bosonic specializations, and remaining analytic blockers are
recorded in [`second-quantization-common-audit.md`](second-quantization-common-audit.md).

## Shared statistics-independent layer

The following infrastructure is shared by both statistics. The listed modules live under the
matching `Common/Algebra/`, `Common/ImaginaryTime/`, `Common/Thermal/`, or
`Common/Diagrammatics/` directory, or in the upstream `Analysis/` and `Combinatorics/` layers.

| Area | Main modules | Current result |
|---|---|---|
| Algebraic Fock space | `Common/Algebra/AlgebraicFock.lean` | Basis states, matrix coefficients, diagonal operators, and linear-map extensionality are generic in the configuration type. |
| Free evolution | `Common/ImaginaryTime/DiagonalEvolution.lean` | Basis-diagonal evolution and algebraic Heisenberg evolution are generic in the energy function. |
| Interaction picture | `Common/ImaginaryTime/InteractionPicture.lean` | The operator construction, matrix-coefficient closed form, continuity, and interval integrability are generic in the configuration type and use only finite support of algebraic-Fock vectors. |
| Exchange relations | `Common/Algebra/ExchangeCommutator.lean`, `Common/Algebra/ExchangeAlgebra.lean` | CAR and CCR are represented through the common statistics-dependent `ζ` relation. |
| Thermal functionals | `Analysis/NormalizedEndomorphismFunctional.lean`, `Common/Thermal/NormalizedOperatorFunctional.lean`, `Common/Thermal/WeightedDiagonalFunctional.lean` | The normalized-functional structure is pure linear algebra; Fock-space and weighted-trace specializations remain in Common. |
| Bloch–de Dominicis | `Common/Thermal/BlochDeDominicis/Induction.lean` | The pairing expansion is proved abstractly under the stated eigenoperator, commutator, non-resonance, and functional hypotheses. |
| Quartic diagrams | `Common/Diagrammatics/*.lean`, `Combinatorics/FinpartitionProduct.lean` | Labels, ordered data, connectedness, component restriction/reassembly, decomposition equivalence, component-local orders, global-order decomposition, and component scalar factorization are statistics independent. |
| Ordered-simplex shuffle calculus | `Analysis/BinaryShuffleSlotOrderedSimplex.lean`, `Analysis/FamilyShuffleOrderedSimplex.lean`, `Combinatorics/FamilySlotShuffleDecomposition.lean`, `Common/Diagrammatics/ComponentOrderedSimplexProduct.lean` | Binary shuffles are equivalent to ambient slot shuffles; arbitrary finite-family shuffle sums equal products of local ordered-simplex integrals; the result is transported to `QuarticDiagram.ComponentShuffle`. |

The Common dependency direction is one way: `Fermionic/` and `Bosonic/` may import `Common/`, while
`Common/` must not import either statistics-specific directory. General facts that do not depend on
Fock spaces, particle statistics, or diagram data belong in `Analysis/` or `Combinatorics/`.

## Fermionic line

The fermionic line currently includes:

- free imaginary-time evolution and arbitrary interaction-picture matrix coefficients
  (`Fermionic/ImaginaryTime/ImaginaryTimeEvolution.lean`,
  `Fermionic/ImaginaryTime/InteractionPicture.lean`);
- finite-basis thermal weights, partition/two-point functions, contractions, concrete
  Bloch–de Dominicis checks, and the occupation-cumulant bridge (`Fermionic/Thermal/`);
- genuine finite-basis Dyson coefficients and partition-series coefficients
  (`Fermionic/Perturbation/DysonExpansion.lean`,
  `Fermionic/Perturbation/DysonPartitionSeries.lean`);
- a general quartic interaction and local-leg semantics
  (`Fermionic/Diagrammatics/QuarticInteraction.lean`,
  `Fermionic/Diagrammatics/QuarticLocalLeg.lean`);
- ordered quartic Wick-diagram amplitudes and the Dyson diagram expansion
  (`Fermionic/Diagrammatics/WickDiagram/Amplitude.lean`,
  `Fermionic/Diagrammatics/DysonDiagramExpansion.lean`);
- component decomposition equivalence and scalar-prefactor factorization
  (`Fermionic/Diagrammatics/WickDiagram/ComponentDecompositionEquiv.lean`,
  `Fermionic/Diagrammatics/WickDiagram/AmplitudePrefactorFactorization.lean`);
- component-local vertex orders, global-order decomposition, component-shuffle integrands, binary and
  finite-family slot shuffles, and the general component ordered-simplex product identity.

The statistics-independent ordered-simplex/component-shuffle milestone is complete. Full
Wick-amplitude factorization now has one diagram-specific block remaining: prove that fermionic
pairing sets, pair values, pair products, and pairing weights factor under assembled component-local
orders.

The pairing-weight theorem is the main risk because `Pairing.weight` is not invariant under arbitrary
relabeling; the proof must exploit the special block-of-four leg permutation induced by vertex
shuffles.

## Fermionic LCT milestones

The detailed exit theorems and work packages are in
[`linked-cluster-theorem.md`](linked-cluster-theorem.md).

| Milestone | Deliverable | Status |
|---|---|---|
| M0 | Statistics-independent component-shuffle product calculus | complete through PR #247 |
| M1 | Fermionic contraction-integrand factorization | next |
| M2 | Full quartic Wick-amplitude factorization | blocked by M1 |
| M3 | Connected-diagram formula for `dysonVertexCumulant` | blocked by M2 |
| M4 | General finite-set cumulant / formal-`log` EGF bridge | independent high-risk track |
| M5 | Final Dyson LCT theorem and Fermionic API export | blocked by M3 and M4 |

The remaining dependency order is:

1. pairing restriction, local leg/pair-value compatibility, global pair-product reindexing, and
   pairing-sign factorization;
2. contraction-integrand and complete `quarticWickDiagramAmplitude` factorization;
3. concrete `Combinatorics.WeightedDiagramFamily` and the connected-diagram finite-set cumulant
   theorem;
4. the general exponential-generating-series bridge between finite-set cumulants and coefficients of
   `formalLogPartitionFunction`;
5. specialization to the normalized Dyson partition series and the final LCT.

The M4 EGF track can proceed in parallel with M1–M3. The two highest-risk blocks are fermionic
pairing-sign factorization and the finite-set cumulant/`PowerSeries.log` coefficient bridge. The
expected remaining implementation is roughly six to nine focused PRs.

## Bosonic line

The bosonic line currently includes:

- occupation states, algebraic Fock space, ladder operators, CCR, number operators, grading, the
  public exchange-commutator bridge, and same-charge diagonal selection rules (`Bosonic/Algebra.lean`);
- free time ordering, diagonal evolution, evolved ladder operators, composition preservation, and the
  algebraic interaction-picture operator with arbitrary matrix-coefficient, continuity, and
  interval-integrability formulas (`Bosonic/ImaginaryTime.lean`);
- convergent free partition and particle-number series, free two-point coefficients, and an uncutoff
  two-point Bloch–de Dominicis specialization (`Bosonic/Thermal.lean`);
- quartic interaction vertices and their interaction-picture formulas, local-leg CCR semantics,
  flattened leg families, ordered diagram data, component decomposition equivalence, and
  componentwise scalar weights (`Bosonic/Diagrammatics.lean`).

Thus the bosonic line matches the fermionic line through the algebraic quartic-diagram layer and the
scalar coupling/Dyson prefactor. It does not yet include the general Dyson coefficient, full quartic
Wick amplitude, or Dyson diagram expansion.

## Parity matrix

| Capability | Fermionic | Bosonic | Reason for any gap |
|---|---:|---:|---|
| Algebraic Fock and ladder operators | done | done | — |
| CAR/CCR through Common exchange algebra | done | done | — |
| Free imaginary-time evolution | done | done | — |
| Algebraic interaction-picture operator | done | done | — |
| Arbitrary interaction-picture matrix-coefficient formula | done | done | Shared through Common and exposed under both statistics-specific APIs. |
| Free thermal two-point result | done | done | Bosonic proof supplies explicit summability. |
| General finite-temperature pairing theorem | done | instantiated at two point | Arbitrary bosonic Gibbs functionals need a convergence-aware domain. |
| Quartic local-leg and ordered-diagram data | done | done | — |
| Component decomposition equivalence | done | done | Shared through Common. |
| Coupling/Dyson scalar-prefactor factorization | done | done | Shared component combinatorics. |
| Binary ordered-simplex shuffle identity | done | reusable | Pure `Analysis`/`Combinatorics`; no statistics-specific input. |
| Finite-family component-shuffle product identity | done | reusable | Pure `Analysis`/`Combinatorics` with a Common diagram specialization. |
| Full quartic Wick amplitude | done | pending | Depends on a bosonic expectation/contraction layer. |
| Dyson diagram expansion | done | pending | Depends on bosonic Dyson coefficients and the full amplitude. |
| Full amplitude factorization | pending | pending | Fermionic pairing compatibility and sign factorization remain; the ordered-simplex component product is complete. |
| Connected-diagram finite-set cumulant theorem | abstract theorem done; concrete instance pending | pending | Fermionic instance needs full amplitude factorization. |
| Formal-log coefficient bridge | pending | pending | General EGF/set-partition theorem remains. |

## Analytic blockers

The remaining bosonic gaps should not be filled by adding a false finite-type assumption.

1. **Operator-valued integration.**
   `Common/Perturbation/FiniteOperatorIntegral.lean` reconstructs an operator by summing over all
   output basis states and therefore assumes `[Fintype Config]`. The bosonic version needs a locally
   finite or summability-controlled operator class.
2. **Gibbs expectations of arbitrary operators.**
   The existing bosonic thermal results prove summability for specific diagonal and two-point
   expressions. A reusable arbitrary-operator functional must carry its summability hypotheses in
   the type or theorem statement.
3. **Completed-space operator theory.**
   Hilbert-space completion, domains of unbounded ladder operators, and trace-class theory remain
   deferred to Track C; the current Track D results are algebraic unless a theorem explicitly states
   a convergent series.

## Recommended implementation order

The fermionic LCT remains the critical path:

1. prove pairing/pair-value compatibility, pair-product reindexing, and pairing-sign factorization;
2. complete fermionic contraction-integrand and amplitude factorization;
3. instantiate the concrete weighted diagram family and obtain the connected-diagram finite-set
   cumulant theorem;
4. prove the general finite-set cumulant/formal-log EGF bridge, in parallel when useful;
5. specialize to the Dyson partition series and export the final fermionic LCT.

After that milestone, resume the convergence-aware bosonic path:

6. define a summability-restricted bosonic thermal functional and prove its linearity, normalization,
   and KMS rotation properties;
7. introduce a compatible bosonic operator-integral/Dyson interface;
8. implement the bosonic quartic Wick amplitude and Dyson diagram expansion;
9. reuse the statistics-independent component-shuffle and connectedness infrastructure where its
   hypotheses are available.
