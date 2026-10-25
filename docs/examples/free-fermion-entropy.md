# Finite grand-canonical free-fermion entropy

For a finite mode type, one-particle energies `ε : Mode → ℝ`, inverse temperature `β`,
and explicit chemical potential `μ`, the grand-canonical Gibbs generator on the full
occupation Fock space is

```text
K(n) = E(n) - μ N(n),    ξᵢ = εᵢ - μ,
fᵢ = 1 / (exp(β ξᵢ) + 1).
```

This is not the sharp-particle-number canonical ensemble. The physical Hamiltonian
remains `H`; `K = H - μN` determines the equilibrium weights, not the real-time generator.

The theorem uses the existing
`QuantumTheory.eigenbasisGibbsDensityOperator`, specialized to
`Common.finiteHilbertBasis` and `Common.grandCanonicalEnergy ε μ`. There is no
additional finite fermionic density-state constructor. The generic entropy identity gives

```text
S = β ⟨K⟩ + log Ξ.
```

The common grand-canonical partition function and its finite-mode fermionic
factorization give

```text
Ξ = ∏ᵢ (1 + exp(-β ξᵢ)),   ⟨K⟩ = ∑ᵢ ξᵢ fᵢ.
```

Combining these identities yields

```text
S = ∑ᵢ [-fᵢ log fᵢ - (1-fᵢ) log(1-fᵢ)].
```

The physical, explicit-`μ` entropy endpoint is

```lean
SecondQuantization.Fermionic.
  vonNeumannEntropy_finiteGrandCanonicalGibbs_toReal_eq_sum_fermiDirac
```

The result is finite-mode and finite-dimensional. It does not claim
factorization for a single fixed-`N` sector or the thermodynamic limit.
