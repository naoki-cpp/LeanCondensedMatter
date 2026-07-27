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

## Shared statistics-independent layer

The following infrastructure is shared by both statistics:

| Area | Main modules | Current result |
|---|---|---|
| Algebraic Fock space | `Common/AlgebraicFock.lean` | Basis states, matrix coefficients, diagonal operators, and linear-map extensionality are generic in the configuration type. |
| Free evolution | `Common/DiagonalEvolution.lean` | Basis-diagonal evolution and algebraic Heisenberg evolution are generic in the energy function. |
| Interaction picture | `Common/InteractionPicture.lean` | The operator construction and zero-time identity are generic; the current matrix-coefficient closed form still assumes `[Fintype Config]`. |
| Exchange relations | `Common/ExchangeCommutator.lean`, `Common/ExchangeAlgebra.lean` | CAR and CCR are represented through the common statistics-dependent `ζ` relation. |
| Bloch–de Dominicis | `Common/BlochDeDominicis/Induction.lean` | The pairing expansion is proved abstractly under the stated eigenoperator, commutator, non-resonance, and functional hypotheses. |
| Quartic diagrams | `Common/QuarticDiagram*.lean` | Labels, ordered data, connectedness, component restriction, reassembly, decomposition equivalence, vertex-local product factorization, and component sign factorization are statistics independent. |

The Common dependency direction is one way: `Fermionic/` and `Bosonic/` may import `Common/`, while
`Common/` must not import either statistics-specific directory.

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
| Arbitrary interaction-picture matrix-coefficient formula | done | pending | Current Common proof uses `[Fintype Config]`. |
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

1. **Matrix coefficients of compositions on an infinite basis.**
   `Common.matrixCoeff_heisenbergEvolve` currently uses the finite-basis composition formula. A
   non-`Fintype` replacement must express the coefficient using the finite support actually produced
   by an algebraic operator, or impose a suitable locally finite condition.
2. **Operator-valued integration.**
   `Common.operatorIntervalIntegral` reconstructs an operator by summing over all output basis
   states and therefore assumes `[Fintype Config]`. The bosonic version needs a locally finite or
   summability-controlled operator class.
3. **Gibbs expectations of arbitrary operators.**
   The existing bosonic thermal results prove summability for specific diagonal and two-point
   expressions. A reusable arbitrary-operator functional must carry its summability hypotheses in
   the type or theorem statement.
4. **Completed-space operator theory.**
   Hilbert-space completion, domains of unbounded ladder operators, and trace-class theory remain
   deferred to Track C; the current Track D results are algebraic unless a theorem explicitly states
   a convergent series.

## Recommended implementation order

1. Generalize the matrix coefficient of operator composition beyond `[Fintype Config]`, using finite
   output support or an explicit locally finite operator condition.
2. Restore the bosonic interaction-picture matrix-coefficient continuity theorem from that result.
3. Define a summability-restricted bosonic thermal functional and prove its linearity, normalization,
   and KMS rotation properties.
4. Introduce a compatible bosonic operator-integral/Dyson interface.
5. Implement the bosonic quartic Wick amplitude and Dyson diagram expansion.
6. Finish the statistics-independent ordered-simplex shuffle and full amplitude factorization.
7. Connect the diagram cumulant identity to coefficients of the normalized formal `log Z`.
