import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Mode
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationLinearity
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator

set_option linter.style.header false

/-!
# Basis-independent fermionic algebraic Fock space

The exterior-algebra Fock representation, smeared creation and annihilation operators, CAR,
mode specializations, occupation-representation equivalences, and algebraic second quantization.
This layer does not depend on lattice, transport, finite-volume, or validation modules.
-/
