import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Ladder
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.LadderAnalytic

set_option linter.style.header false

/-!
# Completed bosonic Fock-space infrastructure

The bosonic completed representation is the occupation `ℓ²` space. Single-mode number operators
and the free Hamiltonian are realized as maximal diagonal `LinearPMap` operators on explicit
weighted `ℓ²` domains, with algebraic-core compatibility and self-adjointness. Creation and
annihilation are likewise realized as closed, densely defined `LinearPMap` weighted shifts on their
natural square-root occupation domains. They are mutual adjoints and agree with the algebraic ladder
operators on the finite-support core.
-/
