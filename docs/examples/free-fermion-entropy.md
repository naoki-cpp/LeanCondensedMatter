# Finite free-fermion entropy

For a finite mode type and one-particle energies `ε : Mode → ℝ`, the canonical free Gibbs density
operator is diagonal in the occupation basis. The mode occupation is

```text
fᵢ = 1 / (exp(β εᵢ) + 1).
```

The state is the generic finite pure-point Gibbs density operator specialized to the occupation
basis. The generic pure-point entropy theorem supplies

```text
S = β E + log Z.
```

The fermionic specialization then establishes the mode factorization

```text
Z = ∏ᵢ (1 + exp(-β εᵢ)),
E = ∑ᵢ εᵢ fᵢ.
```

Combining these identities yields the binary-entropy decomposition

```text
S(ρfree) = ∑ᵢ [-fᵢ log fᵢ - (1-fᵢ) log(1-fᵢ)].
```

The main declaration is

```lean
SecondQuantization.Fermionic.
  vonNeumannEntropy_freeGibbsDensityOperator_toReal_eq_sum_fermiDirac
```

The result is finite-mode and finite-dimensional. It uses the canonical
`QuantumTheory.DensityOperator` entropy API and does not introduce a parallel weighted-functional
state model or make a thermodynamic-limit claim.
