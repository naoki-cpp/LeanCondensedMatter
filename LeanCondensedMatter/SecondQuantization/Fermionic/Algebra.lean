import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Occupation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FockSpace
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ParticleNumberCharge
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.WeightedNumberOperator

set_option linter.style.header false

/-!
# Fermionic algebra

Occupation states, the algebraic fermionic Fock space, creation and annihilation operators, CAR,
the Common exchange-algebra instance, number operators, and free/interacting Hamiltonians.
-/
