# Roadmap — Fermionic Linked Cluster Theorem

**Status: complete in both formal/algebraic and finite-dimensional analytic forms.**

This page records the completed finite-mode, finite-temperature fermionic Linked Cluster Theorem
(LCT). It complements the broader development narrative in
[`second-quantization.md`](second-quantization.md) and the current architecture summary in
[`second-quantization-status.md`](second-quantization-status.md).

The M0–M5 diagrammatic proof is coefficientwise and formal. A later finite-dimensional analytic
bridge proves that the Dyson coefficient series sums to the genuine interacting partition function
and transfers the connected-diagram identity to derivatives of its local normalized logarithm. Neither
result claims a thermodynamic limit or a completed-space treatment of unbounded operators.

## Final formal theorem

For every nonzero perturbation order `n`, the canonical Fermionic namespace contains

```lean
theorem SecondQuantization.Fermionic.
    factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
      PowerSeries.coeff n
        (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1
```

Equivalently, writing

```text
Z_D(λ) = ∑ₙ Zₙ λⁿ,
Ẑ_D(λ) = Z_D(λ) / Z₀,
W_D(λ) = log Ẑ_D(λ),
```

the theorem says

```text
n! [λⁿ] W_D(λ)
  = sum of amplitudes of connected quartic Wick diagrams on n labelled vertices.
```

The factor `n!` converts the ordinary power-series coefficients of `Ẑ_D` into the exponential-
generating normalization used by labelled finite-set partitions.

## Final analytic theorem

For finite fermionic mode sets, define the genuine interacting partition function

```text
Z(λ) = Tr(exp(-β(H₀ + λV)))
```

and choose the local logarithm branch of `Z(λ) / Z(0)` through `log 1 = 0`. The analytic endpoint is

```lean
theorem SecondQuantization.Fermionic.
    iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) (hn : n ≠ 0) :
    iteratedDeriv n
        (analyticNormalizedLogPartitionFunction ε β (quarticInteraction g)) 0 =
      ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1
```

Schematically,

```text
(dⁿ/dλⁿ)|₀ log(Z(λ) / Z(0))
  = sum of amplitudes of connected quartic Wick diagrams on n labelled vertices.
```

The supporting analytic declarations include:

- `hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction`;
- `hasFPowerSeriesAt_analyticDysonPartitionFunction`;
- `analyticAt_analyticNormalizedLogPartitionFunction_zero`;
- `iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff`.

Thus the formal theorem remains the coefficientwise combinatorial core, while the analytic theorem is
the physical finite-mode endpoint.

## Milestone summary

| Milestone | Deliverable | Status | Main completion |
|---|---|---|---|
| M0 | Statistics-independent component-shuffle product calculus | complete | PRs #233–#247 |
| M1 | Fermionic contraction-integrand factorization | complete | through PR #256; later cleanup through PR #282 |
| M2 | Full quartic Wick-amplitude factorization | complete | PR #287 |
| M3 | Connected-diagram formula for `dysonVertexCumulant` | complete | PR #291 |
| M4 | Finite-set cumulant / formal-`log` EGF bridge | complete | PR #295 |
| M5 | Final formal Dyson LCT specialization | complete | PR #299 |
| A0 | Finite-dimensional analytic Dyson and LCT bridge | complete | analytic perturbation modules |

## Dependency chain

```text
component-local orders + component shuffles
                    │
                    ▼
M0: ordered-simplex shuffle sums factor
                    │
                    ▼
M1: contraction integrands factor by component
                    │
                    ▼
M2: complete quartic Wick amplitudes factor by component
                    │
                    ▼
M3: finite-set Dyson cumulants equal connected-diagram sums
                    │
                    ├──────────────┐
                    │              │
                    │              ▼
                    │        M4: n! [λⁿ] log Z equals
                    │            the finite-set cumulant
                    │              │
                    └───────┬──────┘
                            ▼
                    M5: formal Dyson LCT
                            │
                            ▼
              A0: convergent finite-dimensional
                  Dyson series + analytic log bridge
                            │
                            ▼
                    analytic Dyson LCT
```

## M0 — Component-shuffle product calculus

The statistics-independent layer decomposes a global vertex order into component-local orders and a
`QuarticDiagram.ComponentShuffle`. Binary and finite-family slot-shuffle results then give the exit
theorem

```lean
QuarticDiagram.sum_componentShuffle_orderedSimplexIntegral_eq_prod
```

with schematic form

```text
∑ global component shuffles (global ordered-simplex integral)
  = ∏ components (local ordered-simplex integral).
```

This milestone lives in `Analysis/`, `Combinatorics/`, and `SecondQuantization/Common/Diagrammatics/`
and is reusable independently of fermionic signs.

## M1 — Fermionic contraction-integrand factorization

For assembled component-local orders and a component shuffle,

```lean
QuarticWickDiagram.contractionIntegrand_assembleVertexOrder_eq_prod_components
```

proves schematically

```text
contractionIntegrand(d, assembled order, τ)
  = ∏ B contractionIntegrand(d restricted to B, local order B, restricted τ).
```

The proof includes:

- restriction of ordered legs and pairing sets;
- compatibility of component-local pair values;
- reindexing the global normalized-pair product as a product over components;
- fermionic pairing-sign factorization;
- even cross-component parity for permutations of quartic blocks, because exchanging two vertex
  blocks exchanges `4 × 4 = 16` ordered-leg pairs.

No new sign convention was introduced.

## M2 — Full quartic Wick-amplitude factorization

The M0 ordered-simplex theorem, the M1 contraction-integrand theorem, and the existing scalar
prefactor factorization combine to give

```lean
quarticWickDiagramAmplitude_eq_prod_restrictComponentConnected
```

with

```text
A(d) = ∏ B in componentPartition(d), A(d restricted to B).
```

This is the multiplicativity hypothesis required by the abstract weighted-diagram connectedness
machinery.

## M3 — Connected-diagram formula for finite-set cumulants

Quartic Wick diagrams instantiate `Combinatorics.WeightedDiagramFamily` by taking

```text
Diagram S          = QuarticWickDiagram Mode N S,
ConnectedDiagram S = ConnectedQuarticWickDiagram Mode N S,
diagramWeight       = quarticWickDiagramAmplitude ε β g.
```

The component-decomposition equivalence supplies the decomposition, and M2 supplies weight
multiplicativity. Combining the abstract connectedness theorem with the Dyson diagram expansion gives

```lean
dysonVertexCumulant_quarticInteraction_eq_sum_connectedQuarticWickDiagramAmplitude
```

for every nonempty vertex set `S`:

```text
dysonVertexCumulant(S)
  = ∑ connected diagrams on S, amplitude(diagram).
```

## M4 — Formal-log coefficients and finite-set cumulants

The reusable module `Combinatorics/PowerSeriesCumulant.lean` is independent of second quantization.
For a normalized power series `Z` and `n ≠ 0`, it proves

```lean
Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment_fin
```

with

```text
n! [λⁿ] log Z
  = cumulantFromMoment
      (S ↦ |S|! [λ^|S|] Z)
      univ.
```

The proof avoids an explicit closed formula for the partition-lattice Möbius function. Instead it
proves the same recurrence on both sides:

1. `(log Z)' · Z = Z'` gives the binomial recurrence for factorial-normalized coefficients.
2. A set partition is decomposed into the block containing a distinguished element and a partition of
   its complement.
3. Strong induction and the existing moment–cumulant inversion identify the two recurrences.

## M5 — Final formal Dyson specialization

For the normalized Dyson partition series,

```text
coeff n (normalizePartitionSeries (dysonPartitionSeries ε β V))
  = normalizedDysonPartitionCoeff ε β V n.
```

Therefore the M4 finite-set moment is exactly `dysonVertexMoment`, and its cumulant is
`dysonVertexCumulant`. Applying M3 to `V = quarticInteraction g` yields the final formal theorem.

The formal theorem is exported through

```lean
LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics
```

and the full API is available through

```lean
LeanCondensedMatter.SecondQuantization
```

## A0 — Analytic Dyson and logarithm bridge

The finite-dimensional Common perturbation layer constructs the norm-convergent analytic Dyson
evolution and proves the exponential identity. The fermionic specialization then shows:

1. the specialized Dyson trace coefficients sum to
   `analyticDysonPartitionFunction ε β V λ`;
2. those coefficients form its Taylor series with infinite radius;
3. the normalized partition function equals `1` at zero coupling and admits a local analytic
   logarithm;
4. analytic logarithmic derivatives and formal logarithm coefficients satisfy the same triangular
   moment–cumulant recurrence;
5. the formal M5 theorem therefore yields the analytic connected-diagram theorem.

The analytic modules are exported through

```lean
LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation
```

and the full top-level entry point.

## Definition of done

The finite-mode fermionic LCT milestone is complete because:

- the final formal and analytic theorems are public through canonical leaf umbrellas and the single
  top-level SecondQuantization entry point;
- they assume finite `Mode`, the existing order/typeclass hypotheses, and `n ≠ 0`;
- the analytic theorem additionally assumes `0 ≤ β`;
- all intermediate declarations compile without `sorry`;
- `quarticWickDiagramAmplitude` retains its existing sign, coupling, integration, and factorial
  conventions;
- repository-wide Lean CI, no-`sorry`, and theorem-catalog checks passed on the completion work.

## Next work

The completed results should now be treated as the base for separate follow-up tracks.

### 1. Low-order verification

Specialize the formal and analytic theorems at `n = 1, 2, 3` and compare the identities

```text
1! [λ] log Z = z₁,
2! [λ²] log Z = 2 z₂ - z₁²,
3! [λ³] log Z = 6 z₃ - 6 z₁ z₂ + 2 z₁³
```

with explicit connected-diagram enumeration. These are useful regression tests, not prerequisites for
the general theorem.

### 2. Correlation functions and external legs

Extend the connectedness result from the vacuum/free-energy sector to time-ordered correlation
functions, Green functions, sources, and diagrams with external legs.

### 3. Bosonic perturbation theory

The bosonic line needs summability-aware Gibbs functionals and a compatible operator-integration
interface before the existing Common diagram/cumulant machinery can be instantiated.

### 4. Infinite-dimensional extensions

Infinite-mode and completed-space extensions require trace-class, unbounded-operator, and domain
infrastructure. Thermodynamic limits should remain a separate analytic target.

### 5. Canonical API consolidation

Complete issue #345 by removing remaining duplicate wrappers, making the analytic finite-mode theorem
the canonical perturbative endpoint, and finishing migration documentation and architecture checks.
