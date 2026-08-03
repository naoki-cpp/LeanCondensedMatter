# Canonical quantum density-state architecture

Issue: #483

The project now treats spectral trace-class density states as the standard quantum-theory model.
Finite-dimensionality is an additional hypothesis on the same type, not a separate state model.
This migration is intentionally breaking and provides no compatibility aliases or legacy import
modules.

## Canonical public API

The standard declarations live directly in `QuantumTheory`:

- `QuantumTheory.DensityOperator`
- `QuantumTheory.DensityOperator.expectation`
- `QuantumTheory.POVM`
- `QuantumTheory.probSelfAdjoint`
- `QuantumTheory.prob`
- `QuantumTheory.pure`
- `QuantumTheory.vonNeumannEntropy`
- `QuantumTheory.gibbsState`
- `QuantumTheory.energyExpValue`

`QuantumTheory.TraceClass` is not a public namespace. The phrase `trace class` remains valid in the
operator-ideal implementation layer, including `Analysis.Operator.TraceClass` and
`ContinuousLinearMap.SpectralTraceClass`.

## Module ownership

```text
QuantumTheory/
├── DensityOperator/
│   ├── Basic.lean
│   ├── Pure.lean
│   ├── Expectation.lean
│   ├── ExpectationOrder.lean
│   └── Diagonal.lean
├── POVM/
│   ├── Basic.lean
│   └── Born.lean
├── Entropy/
│   ├── Basic.lean
│   └── Diagonal.lean
├── FiniteDimensional/
│   ├── Expectation.lean
│   └── Entropy.lean
└── Gibbs/
    ├── State.lean
    ├── EnergyExpectation.lean
    ├── FreeEnergy.lean
    ├── Entropy.lean
    ├── DiagonalEnergy.lean
    └── Variational.lean
```

`QuantumTheory/DensityOperator.lean` and `QuantumTheory/Entropy.lean` are canonical umbrella
modules, not compatibility shims.

## Finite-dimensional specialization

There is only one density-operator type. Under `[FiniteDimensional ℂ H]`, the project provides
ordinary matrix-trace and entropy-finiteness results for that type:

- `DensityOperator.expectation_eq_linearMap_trace`
- `DensityOperator.linearMap_trace_eq_one`
- `DensityOperator.expectation_eq_sum_diagonal`
- `DensityOperator.entropyOp_hasSummableRealEigenvalues`
- `DensityOperator.vonNeumannEntropy_ne_top`
- `DensityOperator.vonNeumannEntropy_toReal_eq_tsum`

The canonical von Neumann entropy is `ENNReal`-valued because it can diverge in infinite
dimensions. Finite dimensionality proves it is not `⊤` and permits a real-valued `.toReal`
presentation.

## Measurement normalization

The canonical discrete `POVM` accepts any countable outcome type and uses strong pointwise
normalization:

```lean
hasSum_apply : ∀ x, HasSum (fun m => E m x) x
```

Finite-outcome measurements use the same type through the automatic `Countable` instance. The
finite-sum normalization theorem is a specialization of the countable `tsum` theorem.

## Removed APIs

The migration removes:

- the finite-dimensional density-operator subtype based directly on `LinearMap.trace = 1`;
- the finite-only POVM structure and Born implementation;
- the finite real-valued competing entropy definition;
- `QuantumTheory.TraceClass`;
- quantum-theory files whose names end in `TraceClass.lean`;
- conversion layers between finite and trace-class public state types.

## Enforcement

`scripts/check_quantum_theory_architecture.py` rejects:

- `QuantumTheory.TraceClass` references in Lean sources;
- quantum-theory modules ending in `TraceClass.lean`;
- duplicate `DensityOperator` or `POVM` structure declarations;
- compatibility aliases for the removed namespace.

This check runs in both the main Lean CI and the architecture audit workflow.

## Scope boundaries

This migration reorganizes existing bounded density-state theory. It does not add general
measurable POVMs, continuous outcomes, Schatten classes, thermodynamic limits, or unbounded
Hamiltonian domains. Purity remains owned by #437; Gibbs attainment and uniqueness by #438; the
completed-space and unbounded-domain program by #440.
