import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.DiagonalAnalytic

set_option linter.style.header false

/-!
# Completed bosonic Fock-space infrastructure

The bosonic completed representation is the occupation `ℓ²` space. Single-mode number operators
and the free Hamiltonian are realized as maximal diagonal `LinearPMap` operators on explicit
weighted `ℓ²` domains, with algebraic-core compatibility and self-adjointness. Bosonic ladder
operators remain outside the bounded-operator API and require a separate weighted-shift domain
construction.
-/
