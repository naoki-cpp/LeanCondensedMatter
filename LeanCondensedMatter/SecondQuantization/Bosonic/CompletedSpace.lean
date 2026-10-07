import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Ladder
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.LadderAnalytic
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.ProductDomain
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Quartic

set_option linter.style.header false

/-!
# Completed bosonic Fock-space infrastructure

The bosonic completed representation is the occupation `ℓ²` space. Single-mode number operators
and the free Hamiltonian are realized as maximal diagonal `LinearPMap` operators on explicit
weighted `ℓ²` domains, with algebraic-core compatibility and self-adjointness. Creation and
annihilation are likewise realized as closed, densely defined `LinearPMap` weighted shifts on their
natural square-root occupation domains. They are mutual adjoints and agree with the algebraic ladder
operators on the finite-support core. Equal-mode mixed ladder products have maximal domain
`Dom(Nᵢ)`, where they recover `Nᵢ`, `Nᵢ + 1`, and the completed equal-mode CCR. Ordered quartic
vertices are defined as exact domain-aware compositions of four completed ladder operators.
-/
