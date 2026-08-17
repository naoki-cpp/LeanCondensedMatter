import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution

set_option linter.style.header false

/-!
# Abstract quantum balance-law evolution

Public umbrella for particle-statistics-independent conservation-law dynamics. The abstract balance
and current-representation interfaces, together with symmetric-localization algebra, live upstream
under `Analysis`. This layer supplies only the Heisenberg normalization

```text
δₕ(A) = (i / ℏ) [h,A].
```

Spatial localization, distinguished velocity operators, and conventional-current realizations are
owned downstream by concrete models such as `QuantumMechanics.SingleParticle`.
-/
