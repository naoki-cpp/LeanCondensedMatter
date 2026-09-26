import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution

set_option linter.style.header false

/-!
# Abstract quantum balance-law evolution

Particle-statistics-independent conservation-law dynamics in the Heisenberg picture, with
normalization

```text
δₕ(A) = (i / ℏ) [h, A].
```

The underlying balance-law and current-representation interfaces are mathematical structures from
`Analysis`; concrete spatial and current realizations belong to downstream physical models.
-/
