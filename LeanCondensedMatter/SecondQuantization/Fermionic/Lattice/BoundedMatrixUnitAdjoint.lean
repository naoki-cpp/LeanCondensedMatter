import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Bounded
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.RankOneSecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.FiniteHilbertCreationAnnihilation
import Mathlib.Analysis.Matrix.Hermitian

set_option linter.style.header false

/-!
# Adjoint reversal for second-quantized lattice matrix units

The basis-independent identity

```text
AlgebraicFock.dGamma (|x><y|) = a†(x) a(y)
```

is transported through the canonical occupation equivalence and then to the finite-dimensional
Hilbert Fock space. Since bounded occupation creation and annihilation are mutual adjoints, the
resulting matrix-unit operator has the expected adjoint:

```text
(AlgebraicFock.dGamma (|x><y|))† = AlgebraicFock.dGamma (|y><x|).
```

This module supplies the structural input for deriving self-adjoint hopping Hamiltonians and bond
currents from coefficient-level Hermiticity.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

variable {Site : Type*}

variable [LinearOrder Site]

section Finite

variable [Fintype Site]

/-- Bounded finite-Hilbert realization of a second-quantized one-particle matrix unit. -/
noncomputable def boundedDgammaMatrixUnit (x y : Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedLatticeOperator (AlgebraicFock.dGamma ((Site →₀ ℂ)) (matrixUnit x y))

/-- The bounded matrix-unit realization is the finite-Hilbert creation-annihilation bilinear. -/
theorem boundedDgammaMatrixUnit_eq_create_comp_annihilate (x y : Site) :
    boundedDgammaMatrixUnit x y =
      (finiteHilbertCreate x).comp (finiteHilbertAnnihilate y) := by
  change Common.finiteHilbertOperatorAlgEquiv
      (AlgebraicFock.occupationConjugate (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))
        (AlgebraicFock.dGamma ((Site →₀ ℂ)) (matrixUnit x y))) = _
  rw [occupationConjugate_dGamma_matrixUnit,
    finiteHilbertCreate, finiteHilbertAnnihilate]
  simpa only [← Module.End.mul_eq_comp, ← ContinuousLinearMap.mul_def] using
    map_mul (Common.finiteHilbertOperatorAlgEquiv (Config := Occupation Site))
      (create x) (annihilate y)

/-- On the one-particle occupation basis, the bounded second-quantized matrix unit sends the
singleton state at `y` to the singleton state at `x`. -/
@[simp]
theorem boundedDgammaMatrixUnit_apply_singleton (x y : Site) :
    boundedDgammaMatrixUnit x y
        (Common.finiteHilbertBasisState ({y} : Occupation Site)) =
      Common.finiteHilbertBasisState ({x} : Occupation Site) := by
  rw [boundedDgammaMatrixUnit_eq_create_comp_annihilate]
  change finiteHilbertCreate x
      (finiteHilbertAnnihilate y
        (Common.finiteHilbertBasisState ({y} : Occupation Site))) = _
  have hy : fermionSign y ({y} : Occupation Site) = 1 := by
    calc
      fermionSign y ({y} : Occupation Site) =
          fermionSign y (insertOccupation y (vacuum : Occupation Site)) := by
        simp [insertOccupation, vacuum]
      _ = fermionSign y (vacuum : Occupation Site) :=
        fermionSign_insertOccupation_of_not_lt (lt_irrefl y)
      _ = 1 := fermionSign_vacuum y
  rw [finiteHilbertAnnihilate_basisState_of_mem (by simp), hy]
  simp only [Int.cast_one, one_smul]
  rw [finiteHilbertCreate_basisState_of_not_mem (by simp [removeOccupation])]
  simp [fermionSign, removeOccupation, insertOccupation]

/-- A bounded second-quantized matrix unit kills a one-particle singleton state whose occupied site
is not its source site. -/
@[simp]
theorem boundedDgammaMatrixUnit_apply_singleton_of_ne (x y z : Site) (h : z ≠ y) :
    boundedDgammaMatrixUnit x y
        (Common.finiteHilbertBasisState ({z} : Occupation Site)) = 0 := by
  rw [boundedDgammaMatrixUnit_eq_create_comp_annihilate]
  change finiteHilbertCreate x
      (finiteHilbertAnnihilate y
        (Common.finiteHilbertBasisState ({z} : Occupation Site))) = 0
  rw [finiteHilbertAnnihilate_basisState_of_not_mem]
  · exact map_zero _
  · simpa [eq_comm] using h

/-- Taking the Hilbert-space adjoint reverses the oriented one-particle matrix unit. -/
@[simp]
theorem star_boundedDgammaMatrixUnit (x y : Site) :
    star (boundedDgammaMatrixUnit x y) = boundedDgammaMatrixUnit y x := by
  rw [boundedDgammaMatrixUnit_eq_create_comp_annihilate,
    boundedDgammaMatrixUnit_eq_create_comp_annihilate]
  change
    star (finiteHilbertCreate x * finiteHilbertAnnihilate y) =
      finiteHilbertCreate y * finiteHilbertAnnihilate x
  rw [star_mul, star_finiteHilbertAnnihilate, star_finiteHilbertCreate]

/-- A Hermitian finite one-particle coefficient matrix lifts to a self-adjoint
observable on the entire fermionic Fock space. The proof uses only the canonical
adjoint reversal of the second-quantized matrix units. -/
theorem isSelfAdjoint_sum_boundedDgammaMatrixUnit
    (A : Matrix Site Site ℂ) (hA : A.IsHermitian) :
    IsSelfAdjoint
      (∑ i : Site, ∑ j : Site, A i j • boundedDgammaMatrixUnit i j) := by
  have hentry (i j : Site) : star (A j i) = A i j := by
    have h := congrArg (fun B : Matrix Site Site ℂ => B i j) hA.star_eq
    simpa [Matrix.conjTranspose_apply] using h
  rw [isSelfAdjoint_iff]
  simp only [star_sum, star_smul, star_boundedDgammaMatrixUnit]
  rw [Finset.sum_comm]
  simp_rw [hentry]

/-- A finite collection of Hermitian internal matrix blocks yields a self-adjoint
full-Fock observable, even when the block-to-mode labels are supplied abstractly. -/
theorem isSelfAdjoint_sum_boundedDgammaMatrixUnit_blocks
    {Block Label : Type*} [Fintype Block] [Fintype Label]
    (site : Block → Label → Site)
    (blocks : Block → Matrix Label Label ℂ)
    (hblocks : ∀ k, (blocks k).IsHermitian) :
    IsSelfAdjoint
      (∑ k : Block, ∑ a : Label, ∑ b : Label,
        blocks k a b • boundedDgammaMatrixUnit (site k a) (site k b)) := by
  have hentry (k : Block) (a b : Label) :
      star (blocks k b a) = blocks k a b := by
    have h := congrArg (fun B : Matrix Label Label ℂ => B a b) (hblocks k).star_eq
    simpa [Matrix.conjTranspose_apply] using h
  rw [isSelfAdjoint_iff]
  simp only [star_sum, star_smul, star_boundedDgammaMatrixUnit]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp_rw [hentry k]

/-- The existing finite-lattice hopping Hamiltonian is self-adjoint whenever
its one-particle hopping amplitudes are Hermitian. -/
theorem isSelfAdjoint_boundedHoppingHamiltonian
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes) :
    IsSelfAdjoint (boundedHoppingHamiltonian K) := by
  let A : Matrix Site Site ℂ := fun x y => K.amplitude x y
  have hA : A.IsHermitian := by
    change Matrix.conjTranspose A = A
    apply Matrix.ext
    intro x y
    change star (K.amplitude y x) = K.amplitude x y
    exact hK y x
  have hsum : boundedHoppingHamiltonian K =
      ∑ x : Site, ∑ y : Site, A x y • boundedDgammaMatrixUnit x y :=
    boundedHoppingHamiltonian_eq_sum_matrixUnit K
  rw [hsum]
  exact isSelfAdjoint_sum_boundedDgammaMatrixUnit A hA

end Finite

end
end Lattice
end Fermionic
end SecondQuantization
