# Second Quantization — Current Status

This page is the current-state companion to
[`second-quantization.md`](second-quantization.md), which retains the longer development narrative and
phase history. The source of truth for each completed claim is the referenced Lean module and
declaration; all files listed below compile without `sorry`.

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

Sources: `Fermionic/Occupation.lean`, `Bosonic/Algebra.lean`,
`Common/WeightedDiagonalFunctional.lean`, and `Common/FiniteOperatorIntegral.lean`.

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

The Common API uses five corresponding responsibility groups:

| Common import | Scope |
|---|---|
| `SecondQuantization.Common.Algebra` | Algebraic Fock infrastructure, statistics, grading, and CAR/CCR interfaces. |
| `SecondQuantization.Common.ImaginaryTime` | Time ordering, diagonal evolution, interaction pictures, and KMS rotation. |
| `SecondQuantization.Common.Thermal` | Normalized functionals, diagonal traces, Gibbs infrastructure, and Bloch–de Dominicis. |
| `SecondQuantization.Common.Perturbation` | Finite-basis coefficientwise operator integration. |
| `SecondQuantization.Common.Diagrammatics` | Label-generic quartic diagrams and component decomposition. |

The extraction decisions and deferred Bosonic specializations are recorded in
[`second-quantization-common-audit.md`](second-quantization-common-audit.md).

## Shared statistics-independent layer

The following infrastructure is shared by both statistics:

| Area | Main modules | Current result |
|---|---|---|
| Algebraic Fock space | `Common/AlgebraicFock.lean` | Basis states, matrix coefficients, diagonal operators, and linear-map extensionality are generic in the configuration type. |
| Free evolution | `Common/DiagonalEvolution.lean` | Basis-diagonal evolution and algebraic Heisenberg evolution are generic in the energy function. |
| Interaction picture | `Common/InteractionPicture.lean` | The operator construction, matrix-coefficient closed form, continuity, and interval integrability are generic in the configuration type and use only finite support of algebraic-Fock vectors. |
| Exchange relations | `Common/ExchangeCommutator.lean`, `Common/ExchangeAlgebra.lean` | CAR and CCR are represented through the common statistics-dependent `ζ` relation. |
| Thermal functionals | `Analysis/NormalizedEndomorphismFunctional.lean`, `Common/NormalizedOperatorFunctional.lean`, `Common/WeightedDiagonalFunctional.lean` | The normalized-functional structure is pure linear algebra; Fock-space and weighted-trace specializations remain in Common. |
| Bloch–de Dominicis | `Common/BlochDeDominicis/Induction.lean` | The pairing expansion is proved abstractly under the stated eigenoperator, commutator, non-resonance, and functional hypotheses. |
| Quartic diagrams | `Common/QuarticDiagram*.lean`, `Combinatorics/FinpartitionProduct.lean` | Labels, ordered data, connectedness, component restriction/reassembly, decomposition equivalence, and component scalar factorization are statistics independent; the underlying finite-partition product identities are pure combinatorics. |

The Common dependency direction is one way: `Fermionic/` and `Bosonic/` may import `Common/`, while
`Common/` must not import either statistics-specific directory. General facts that do not depend on
Fock spaces, particle statistics, or diagram data belong in `Analysis/` or `Combinatorics/`.

## Fermionic line

The fermionic line currently includes:

- free imaginary-time evolution and arbitrary interaction-picture matrix coefficients
  (`Fermionic/ImaginaryTimeEvolution.lean`, `Fermionic/InteractionPicture.lean`);
- genuine finite-basis Dyson coefficients and partition-series coefficients
  (`Fermionic/DysonExpansion.lean`, `Fermionic/DysonPartitionSeries.lean`);
- a general quartic interaction and local-leg semantics
  (`Fermionic/QuarticInteraction.lean`, `Fermionic/QuarticLocalLeg.lean`);
- ordered quartic Wick-diagram amplitudes and the Dyson diagram expansion
  (`Fermionic/WickDiagram/Amplitude.lean`, `Fermionic/DysonDiagramExpansion.lean`);
- component decomposition equivalence and scalar-prefactor factorization
  (`Fermionic/WickDiagram/ComponentDecompositionEquiv.lean`,
  `Fermionic/WickDiagram/AmplitudePrefactorFactorization.lean`).

The full Wick-amplitude factorization is not complete. The remaining combinatorial/analytic step is
the ordered-simplex shuffle identity together with compatibility of pairing weights and pair-value
products under component-local orders.

## Bosonic line

The bosonic line currently includes:

- occupation states, algebraic Fock space, ladder operators, CCR, number operators, and grading
  (`Bosonic/Algebra.lean`);
- free time ordering, diagonal evolution, evolved ladder operators, and the algebraic
  interaction-picture operator (`Bosonic/ImaginaryTime.lean`);
- convergent free partition and particle-number series, free two-point coefficients, and an uncutoff
  two-point Bloch–de Dominicis specialization (`Bosonic/Thermal.lean`);
- quartic interaction vertices, local-leg CCR semantics, flattened leg families, ordered diagram
  data, component decomposition equivalence, and componentwise scalar weights
  (`Bosonic/Diagrammatics.lean`).

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
| Arbitrary interaction-picture matrix-coefficient formula | done | available through Common | A thin Bosonic-named specialization has not yet been added. |
| Free thermal two-point result | done | done | Bosonic proof supplies explicit summability. |
| General finite-temperature pairing theorem | done | instantiated at two point | Arbitrary bosonic Gibbs functionals need a convergence-aware domain. |
| Quartic local-leg and ordered-diagram data | done | done | — |
| Component decomposition equivalence | done | done | Shared through Common. |
| Coupling/Dyson scalar-prefactor factorization | done | done | Shared component combinatorics. |
| Full quartic Wick amplitude | done | pending | Depends on a bosonic expectation/contraction layer. |
| Dyson diagram expansion | done | pending | Depends on bosonic Dyson coefficients and the full amplitude. |
| Full amplitude factorization | pending | pending | Ordered-simplex shuffle and pairing compatibility remain. |
| Linked-cluster/logarithm bridge | pending | pending | Depends on the completed amplitude factorization. |

## Analytic blockers

The remaining bosonic gaps should not be filled by adding a false finite-type assumption.

1. **Operator-valued integration.**
   `Common.operatorIntervalIntegral` reconstructs an operator by summing over all output basis
   states and therefore assumes `[Fintype Config]`. The bosonic version needs a locally finite or
   summability-controlled operator class.
2. **Gibbs expectations of arbitrary operators.**
   The existing bosonic thermal results prove summability for specific diagonal and two-point
   expressions. A reusable arbitrary-operator functional must carry its summability hypotheses in
   the type or theorem statement.
3. **Completed-space operator theory.**
   Hilbert-space completion, domains of unbounded ladder operators, and trace-class theory remain
   deferred to Track C; the current Track D results are algebraic unless a theorem explicitly states
   a convergent series.

## Recommended implementation order

1. Add thin Bosonic names for the now-generic interaction-picture matrix-coefficient, continuity, and
   interval-integrability theorems where they improve discoverability.
2. Define a summability-restricted bosonic thermal functional and prove its linearity, normalization,
   and KMS rotation properties.
3. Introduce a compatible bosonic operator-integral/Dyson interface.
4. Implement the bosonic quartic Wick amplitude and Dyson diagram expansion.
5. Finish the statistics-independent ordered-simplex shuffle and full amplitude factorization.
6. Connect the diagram cumulant identity to coefficients of the normalized formal `log Z`.
