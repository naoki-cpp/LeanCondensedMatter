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

/-- The canonical exterior basis is the ordered product of its one-particle basis vectors. -/
theorem exteriorBasis_eq_sort_prod
    (b : Module.Basis Mode ℂ 𝓗₁) (n : Finset Mode) :
    b.ExteriorAlgebra n =
      ((n.sort (· ≤ ·)).map fun i => oneParticle 𝓗₁ (b i)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard (n := n.card) b rfl]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    oneParticle, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    List.ofFn_eq_map]
  let t : Set.powersetCard Mode n.card := Set.powersetCard.ofCard rfl
  change
    (List.map
        (fun i : Fin n.card =>
          ExteriorAlgebra.ι ℂ
            (b (((↑t : Finset Mode).orderEmbOfFin t.prop) i)))
        (List.finRange n.card)).prod =
      (List.map (fun x => ExteriorAlgebra.ι ℂ (b x))
        (n.sort (· ≤ ·))).prod
  calc
    _ =
        (List.map (fun x => ExteriorAlgebra.ι ℂ (b x))
          ((List.finRange n.card).map
            ((↑t : Finset Mode).orderEmbOfFin t.prop))).prod := by
      simp only [List.map_map, Function.comp_apply]
    _ = _ := by
      rw [Finset.listMap_orderEmbOfFin_finRange]
      rfl

/-- A basis vector inserted before every occupied mode creates the new exterior-basis state with
no permutation sign. -/
theorem create_exteriorBasis_of_lt
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) (n : Finset Mode)
    (hi : ∀ x ∈ n, i < x) :
    create 𝓗₁ (b i) (b.ExteriorAlgebra n) =
      b.ExteriorAlgebra (insert i n) := by
  have hin : i ∉ n := by
    intro h
    exact (lt_irrefl i) (hi i h)
  have hle : ∀ x ∈ n, i ≤ x := fun x hx => (hi x hx).le
  have hsort :
      (insert i n).sort (· ≤ ·) = i :: n.sort (· ≤ ·) :=
    Finset.sort_insert (r := fun x y : Mode => x ≤ y) hle hin
  rw [create_apply, exteriorBasis_eq_sort_prod b n,
    exteriorBasis_eq_sort_prod b (insert i n), hsort]
  simp only [List.map_cons, List.prod_cons]

/-- A one-particle basis vector is the singleton exterior-basis vector. -/
theorem oneParticle_basis_eq_exteriorBasis_singleton
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    oneParticle 𝓗₁ (b i) = b.ExteriorAlgebra ({i} : Finset Mode) := by
  have h := create_exteriorBasis_of_lt b i (∅ : Finset Mode) (by simp)
  simpa [create_apply, exteriorBasis_eq_sort_prod] using h

/-- Exterior multiplication by a basis vector has the occupation-sign action on exterior-basis
vectors. -/
theorem create_exteriorBasis
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) (n : Finset Mode) :
    create 𝓗₁ (b i) (b.ExteriorAlgebra n) =
      if i ∈ n then 0
      else (fermionSign i n : ℂ) • b.ExteriorAlgebra (insertOccupation i n) := by
  induction n using Finset.induction_on_min generalizing i with
  | empty =>
      have h := create_exteriorBasis_of_lt b i (∅ : Finset Mode) (by simp)
      simpa [fermionSign, insertOccupation] using h
  | insert a s hmin ih =>
      have ha : a ∉ s := by
        intro ha
        exact (lt_irrefl a) (hmin a ha)
      have hbase :
          create 𝓗₁ (b a) (b.ExteriorAlgebra s) =
            b.ExteriorAlgebra (insert a s) :=
        create_exteriorBasis_of_lt b a s hmin
      rw [← hbase]
      by_cases hia : i = a
      · subst i
        rw [if_pos (Finset.mem_insert_self a s)]
        change
          ((create 𝓗₁ (b a)).comp (create 𝓗₁ (b a)))
              (b.ExteriorAlgebra s) = 0
        rw [create_comp_self, LinearMap.zero_apply]
      by_cases his : i ∈ s
      · rw [if_pos (Finset.mem_insert_of_mem his)]
        have hcar := LinearMap.congr_fun
          (create_comp_add_swap 𝓗₁ (b i) (b a)) (b.ExteriorAlgebra s)
        have hiZero := ih i
        rw [if_pos his] at hiZero
        simp only [LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.zero_apply] at hcar
        rw [hiZero, map_zero, add_zero] at hcar
        exact hcar
      · have hiInsert : i ∉ insert a s := by
          simp [hia, his]
        rw [if_neg hiInsert]
        rcases lt_or_gt_of_ne hia with hlt | hgt
        · rw [hbase]
          have hmin' : ∀ x ∈ insert a s, i < x := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hlt
            · exact lt_trans hlt (hmin x hx)
          have hnew := create_exteriorBasis_of_lt b i (insert a s) hmin'
          rw [hnew]
          have hfilter : (insert a s).filter (fun x => x < i) = ∅ := by
            ext x
            simp only [Finset.mem_filter]
            constructor
            · intro hx
              exact (lt_asymm hx.2 (hmin' x hx.1)).elim
            · intro hx
              have hfalse : False := by simpa using hx
              exact hfalse.elim
          simp [fermionSign, hfilter, insertOccupation]
        · have hcar := congrArg
            (fun z => z * b.ExteriorAlgebra s)
            (oneParticle_mul_add_swap 𝓗₁ (b i) (b a))
          have hswap :
              create 𝓗₁ (b i) (create 𝓗₁ (b a) (b.ExteriorAlgebra s)) =
                -create 𝓗₁ (b a) (create 𝓗₁ (b i) (b.ExteriorAlgebra s)) := by
            change
              oneParticle 𝓗₁ (b i) *
                  (oneParticle 𝓗₁ (b a) * b.ExteriorAlgebra s) =
                -(oneParticle 𝓗₁ (b a) *
                  (oneParticle 𝓗₁ (b i) * b.ExteriorAlgebra s))
            rw [add_mul, zero_mul, mul_assoc, mul_assoc] at hcar
            exact eq_neg_of_add_eq_zero_left hcar
          rw [hswap]
          have hiStep := ih i
          rw [if_neg his] at hiStep
          rw [hiStep, map_smul]
          have hamin : ∀ x ∈ insert i s, a < x := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hgt
            · exact hmin x hx
          have haStep := create_exteriorBasis_of_lt b a (insert i s) hamin
          change
            -((fermionSign i s : ℂ) •
                create 𝓗₁ (b a) (b.ExteriorAlgebra (insert i s))) =
              (fermionSign i (insertOccupation a s) : ℂ) •
                b.ExteriorAlgebra
                  (insertOccupation i (insertOccupation a s))
          rw [haStep, fermionSign_insertOccupation_of_lt ha hgt]
          simp [insertOccupation, Finset.insert_comm]

/-- The basis-induced occupation/exterior equivalence intertwines creation on basis states. -/
theorem occupationEquiv_create_basisState
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) (n : Occupation Mode) :
    occupationEquiv b (SecondQuantization.Fermionic.create i (basisState n)) =
      create 𝓗₁ (b i) (occupationEquiv b (basisState n)) := by
  rw [occupationEquiv_basisState]
  by_cases hi : i ∈ n
  · rw [SecondQuantization.Fermionic.create_basisState_of_mem hi, map_zero]
    simpa [hi] using (create_exteriorBasis b i n).symm
  · rw [SecondQuantization.Fermionic.create_basisState_of_not_mem hi, map_smul,
      occupationEquiv_basisState]
    simpa [hi] using (create_exteriorBasis b i n).symm

/-- The basis-induced equivalence intertwines the full creation operators. -/
theorem occupationEquiv_create
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    (occupationEquiv b).toLinearMap.comp
        (SecondQuantization.Fermionic.create i) =
      (create 𝓗₁ (b i)).comp (occupationEquiv b).toLinearMap := by
  apply Finsupp.lhom_ext
  intro n c
  have hsingle : Finsupp.single n c = c • basisState n := by
    ext m
    by_cases hmn : n = m
    · subst m
      simp [basisState, Common.basisState]
    · simp [basisState, Common.basisState, hmn]
  rw [hsingle]
  simp only [map_smul, LinearMap.comp_apply]
  exact congrArg (fun Ψ => c • Ψ) (occupationEquiv_create_basisState b i n)

end
end Field
end Fermionic
end SecondQuantization
