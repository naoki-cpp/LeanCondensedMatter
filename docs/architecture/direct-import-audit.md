# Direct-import audit: dependency intent versus transitive reachability

This audit consolidates the import-cleanup batches and the PR #4312 overlap inventory (November 2026). It supplements
`scripts/export_module_import_graph.py --report-overlaps`, whose output is **advisory**.

## Decision rule

A transitive path `file -> via -> ... -> target` establishes **graph redundancy**
of the `file -> target` edge. It does **not** establish that the direct import is
unnecessary for maintenance, Lean module visibility, scoped attributes, tactics,
instances, or downstream clients.

1. **Retain a direct dependency** when the file's statements or proofs visibly refer
   to declarations *owned by that dependency*, even if another import also makes
   them reachable. This makes source ownership and the intended layer explicit.
2. **Consider deletion** when a retained import already supplies the target and
   source inspection finds no direct use of target-owned declarations. This remains
   a tentative judgment; indirect notation, instances, attributes, and namespace
   effects may escape a lexical check.
3. **Require a full Lean build and downstream checks** after any deletion.
   Do not interpret a successful build as a proof that the resulting module
   boundaries are architecturally preferable.
4. **Do not replace direct imports with a broader umbrella import** simply to
   decrease the line count. Intentional import-only umbrella files are excluded
   from the ordinary implementation-overlap review.

## Batch 7: candidates selected for removal

The right-hand module is an *already-retained* direct import from which the
removed target remains transitively reachable. Source inspection found no
obvious direct reference to declarations owned by the removed module; this
claim is deliberately weaker than a semantic dependency proof.

| Source module (under `LeanCondensedMatter`) | Removed direct import | Retained witness |
| --- | --- | --- |
| `QuantumTheory/DensityOperator/Pure` | `Analysis.Operator.Compact` | `Analysis.Operator.TraceClass.Positive` |
| `QuantumTheory/DensityOperator/Purity` | `QuantumTheory.DensityOperator.ExpectationOrder` | `QuantumTheory.DensityOperator.ObservableExpectation` |
| `QuantumTheory/LinearResponse/Perturbation/Unitary` | `Analysis.Operator.AdjointConjugation` | `QuantumTheory.LinearResponse.Response.KuboFormula` |
| `Permutation/ConnectedDecomposition` | `Combinatorics.SetPartition.FinpartitionProduct` | `Combinatorics.Cumulant.ConnectedDecomposition` |
| `SecondQuantization/Fermionic/Diagrammatics/TwoPointDiagramExpansion/Analysis/DiagramRegularity` | `SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPairEquiv` | `SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentCrossingTimeLocality` |

All five changes are **provisional until CI succeeds**.

## Graph-overlap candidates deliberately retained

These target modules own declarations that are explicitly referenced in the
consumer source. The direct import is useful dependency documentation, even
though the graph analyzer also finds another transitive path.

| Consumer | Retained import | Evidence of direct API use |
| --- | --- | --- |
| `Analysis/Operator/TraceClass/Ops/Basic` | `Analysis.Operator.TraceClass.Factorization.Basic` | `isTraceClass_iff_exists_hilbertSchmidt_factorization` |
| `Analysis/PowerSeries/MomentCumulantRecurrence` | `Analysis.PowerSeries.Normalization` | `PowerSeries.derivative_logOf_mul` |
| `Models/MassiveDirac/Conductivity/Hall/NonCrossingDecomposition` | `QuantumTheory.PlanckConstant` | `planckConstantFromReduced` |
| `QuantumTheory/LinearResponse/Response/ObservableVariation` | `Analysis.Operator.AdjointConjugation` | `ContinuousLinearMap.adjointConjugate` |
| `QuantumMechanics/SingleParticle/Continuum/Continuity/CompactSupport1D` | `Analysis.ConservationLaw.WeakConservation1D` | `integral_mul_eq_integral_of_tsupport_subset_Ioo` |
| `QuantumMechanics/SingleParticle/Continuum/Hamiltonian/Symmetry1D` | `QuantumMechanics.SingleParticle.Continuum.L2.Multiplication1D` | `l2MultiplicationOperator1D` |
| `SecondQuantization/Fermionic/Diagrammatics/ExternalInsertion/DysonSeries` | `Analysis.PowerSeries.Normalization` | `normalizeByConstantCoeff` |
| `SecondQuantization/Fermionic/Diagrammatics/ExternalInsertion/DysonSeries` | `SecondQuantization.Fermionic.Algebra.QuarticInteraction` | `quarticInteraction` |
| `Transport/KuboBastin/Occupation` | `Transport.KuboBastin.Eigenbasis` | `eigenbasisKuboBastinSpectralVertexTerm` |
| `QuantumTheory/Entropy/Basic` | `Analysis.FunctionalCalculus.CFC` | `cfc_apply_eigenvector` |

## Reconciliation with PR #4312 (November 2026)

[PR #4312](https://github.com/naoki-cpp/LeanCondensedMatter/pull/4312)
added a CI artifact of **source-graph overlap candidates**. That artifact
belongs to its original commit, not current `main`. The source audit at
that commit listed **814 total overlap edges**, of which **455 occurred in
import-only umbrellas** and **359 in implementation or other files**.
The later [PR #4660](https://github.com/naoki-cpp/LeanCondensedMatter/pull/4660)
source CI listed **602 total**, **457 in import-only umbrellas** and
**145 in implementation or other files**. The latter report is a dated
snapshot, not a frozen requirement or a claim that 145 imports are unnecessary.

Import pruning across intervening batches explains much of the reduction,
but changing source/module topology also changes transitive overlap counts.
Never subtract these numbers to assert that precisely that many *semantically
unnecessary* imports were removed.

The current report is generated live, for a focused review:

```bash
python3 scripts/export_module_import_graph.py --report-overlaps \
  --source-prefix LeanCondensedMatter/Combinatorics --limit 1000
python3 scripts/export_module_import_graph.py --report-overlaps \
  --source-prefix LeanCondensedMatter/Models/MassiveDirac --limit 1000
```

### Confirmed declaration-owner uses among remaining candidates

The table records *why not to remove* a directly imported declaration owner
merely to make a transitive-overlap count smaller. These were inspected
against the post-#4660 source, not inferred from the #4312 archive.

| Consumer | Direct import retained | Source-level use |
| --- | --- | --- |
| `Combinatorics/Shuffle/FamilySlotShuffleDecomposition` | `Combinatorics.SetPartition.SumEquivPartition` | `SumEquiv.leftImage`, `SumEquiv.rightImage` |
| `Combinatorics/Shuffle/FamilySlotShuffleSign` | `Combinatorics.FiniteSumModEq` | `finset_sum_offDiag_modEq_of_pair_add_modEq` |
| `Combinatorics/PerfectPairing/VertexGraph` | `Combinatorics.PerfectPairing.Transport` | `PairingOn.transport_partner` |
| `SecondQuantization/Common/Thermal/BlochDeDominicis/PairingWeight` | `Combinatorics.PerfectPairing.CrossingEraseZero` | `Pairing.crossingCount_eraseZeroPair` |
| `Models/Heisenberg/SpinWaveSpectrum` | `Analysis.Fourier.CyclicLaplacian` | `ZMod.cyclicLaplacianEigenvalue` |
| `Models/MassiveDirac/Conductivity/Hall/CleanBastin` | `QuantumTheory.PlanckConstant` | `planckConstantFromReduced` |
| `QuantumTheory/LinearResponse/Lehmann/Eigenbasis/FrequencyDomain` | `QuantumTheory.LinearResponse.Lehmann.Transition` | `LehmannTransitionData.adiabaticTimeTerm` |
| `Transport/Reciprocity/Data` | `Analysis.Operator.FiniteTrace` | `finiteDimensionalOperatorTrace` |
| `SecondQuantization/Fermionic/Transport/SpinCurrentResponse` | `QuantumTheory.SpinHalf` | `SpinHalf.SpinSpace` |

These rows are **confirmed source-level references**, not an exhaustive audit
of all 145 historical review candidates. The remaining entries require
declaration ownership and Lean compilation checks before any deletion.
No import should be removed merely because its target is reachable through
another module.

## What is not established

A source-symbol scan can confirm visible uses, but **absence** of a matching
declaration name is not proof of absence of a dependency. Imported instances,
notation, macros, tactic extensions, local attributes, and Mathlib public-import
visibility may all matter. Likewise, a `lake build` does not by itself detect
maintenance cost from hiding a genuine conceptual dependency behind a
transitive import.

The earlier batches removed graph-overlapping imports; their successful CI
checks should **not** be interpreted as a semantic proof that every deleted
edge represented an accidental dependency. A future ownership audit may
restore explicit imports where the consumer directly uses target-owned APIs.
