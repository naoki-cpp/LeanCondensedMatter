import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationLinearity
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationNaturality
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.RankOne
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.FiniteHilbertRealization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.FiniteHilbertIsometry

set_option linter.style.header false

/-!
# Basis-independent fermionic algebraic Fock space

The exterior-algebra Fock representation, smeared creation and annihilation operators, CAR,
occupation-representation equivalences, algebraic second quantization, and
the rank-one factorization `dΓ(|f⟩⟨d|) = a†(f) a(d)`.
The declarations belong to `SecondQuantization.Fermionic.AlgebraicFock`.
This layer does not depend on lattice, transport, finite-volume, or validation modules.
-/
