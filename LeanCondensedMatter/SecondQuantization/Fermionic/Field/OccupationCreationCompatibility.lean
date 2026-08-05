import LeanCondensedMatter.SecondQuantization.Fermionic.Field.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

set_option linter.style.header false

/-!
# Compatibility of occupation and exterior-field creation

The occupation-subset Fock representation and the basis-independent exterior-algebra representation
use the same ordered wedge convention. This module proves that the basis-induced equivalence
intertwines the existing mode creation operator with exterior multiplication by the corresponding
one-particle basis vector.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]
variable {𝓗₁ : Type*} [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- A one-particle basis vector is the singleton exterior-basis vector. -/
theorem oneParticle_basis_eq_exteriorBasis_singleton
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    oneParticle 𝓗₁ (b i) = b.ExteriorAlgebra ({i} : Finset Mode) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (by simp)]
  simp [oneParticle, ExteriorAlgebra.ιMulti_family]

/-- Exterior multiplication by a basis vector has the occupation-sign action on exterior-basis
vectors. -/
theorem create_exteriorBasis
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) (n : Finset Mode) :
    create 𝓗₁ (b i) (b.ExteriorAlgebra n) =
      if i ∈ n then 0
      else (fermionSign i n : ℂ) • b.ExteriorAlgebra (insertOccupation i n) := by
  by_cases hi : i ∈ n
  · rw [if_pos hi, create_apply, oneParticle_basis_eq_exteriorBasis_singleton]
    let s : Set.powersetCard Mode 1 := Set.powersetCard.ofCard (by simp : ({i} : Finset Mode).card = 1)
    let t : Set.powersetCard Mode n.card := Set.powersetCard.ofCard rfl
    have hnot : ¬ Disjoint (↑s : Finset Mode) (↑t : Finset Mode) := by
      simp [s, t, hi]
    simpa [s, t] using ExteriorAlgebra.basis_mul_of_not_disjoint b s t hnot
  · rw [if_neg hi, create_apply, oneParticle_basis_eq_exteriorBasis_singleton]
    let s : Set.powersetCard Mode 1 := Set.powersetCard.ofCard (by simp : ({i} : Finset Mode).card = 1)
    let t : Set.powersetCard Mode n.card := Set.powersetCard.ofCard rfl
    have hdisj : Disjoint (↑s : Finset Mode) (↑t : Finset Mode) := by
      simp [s, t, hi]
    have hmul := ExteriorAlgebra.basis_mul_of_disjoint b s t hdisj
    simpa [s, t, fermionSign, insertOccupation] using hmul

/-- The basis-induced occupation/exterior equivalence intertwines creation on basis states. -/
theorem occupationEquiv_create_basisState
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) (n : Occupation Mode) :
    occupationEquiv b (SecondQuantization.Fermionic.create i (basisState n)) =
      create 𝓗₁ (b i) (occupationEquiv b (basisState n)) := by
  rw [occupationEquiv_basisState, occupationEquiv_basisState]
  by_cases hi : i ∈ n
  · rw [SecondQuantization.Fermionic.create_basisState_of_mem hi, map_zero]
    simp [create_exteriorBasis, hi]
  · rw [SecondQuantization.Fermionic.create_basisState_of_not_mem hi, map_smul,
      occupationEquiv_basisState]
    simp [create_exteriorBasis, hi]

/-- The basis-induced equivalence intertwines the full creation operators. -/
theorem occupationEquiv_create
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    (occupationEquiv b).toLinearMap.comp SecondQuantization.Fermionic.create i =
      (create 𝓗₁ (b i)).comp (occupationEquiv b).toLinearMap := by
  apply linearMap_ext_basisState
  intro n
  exact occupationEquiv_create_basisState b i n

end
end Field
end Fermionic
end SecondQuantization
