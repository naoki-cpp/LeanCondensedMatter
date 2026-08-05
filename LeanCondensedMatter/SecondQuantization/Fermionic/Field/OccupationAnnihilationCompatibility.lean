import LeanCondensedMatter.SecondQuantization.Fermionic.Field.OccupationCreationCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations

set_option linter.style.header false

/-!
# Compatibility of occupation and exterior-field annihilation

Rather than repeating the exterior-basis shuffle-sign computation from creation, annihilation is
identified by a representation-independent uniqueness principle: an operator on occupation Fock
space is `annihilate i` when it kills the vacuum and has the mixed CAR with every creation
operator. The proof of uniqueness is a finite-set induction on occupation basis states.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]
variable {𝓗₁ : Type*} [AddCommGroup 𝓗₁] [Module ℂ 𝓗₁]

/-- Conjugate an exterior-Fock endomorphism into the occupation-subset representation using a
chosen one-particle basis. -/
noncomputable def occupationConjugate
    (b : Module.Basis Mode ℂ 𝓗₁)
    (A : FiniteParticleFock 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (occupationEquiv b).symm.toLinearMap.comp
    (A.comp (occupationEquiv b).toLinearMap)

@[simp]
theorem occupationEquiv_occupationConjugate_apply
    (b : Module.Basis Mode ℂ 𝓗₁)
    (A : FiniteParticleFock 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁)
    (Ψ : FockSpace Mode) :
    occupationEquiv b (occupationConjugate b A Ψ) = A (occupationEquiv b Ψ) := by
  simp [occupationConjugate, LinearMap.comp_apply]

/-- An occupation-Fock endomorphism is uniquely determined as `annihilate i` by its vacuum value
and mixed CAR with all creation operators. -/
theorem eq_annihilate_of_vacuum_of_mixedCAR
    (B : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (i : Mode)
    (hVac : B (basisState (∅ : Occupation Mode)) = 0)
    (hCAR : ∀ (j : Mode) (n : Occupation Mode),
      B (SecondQuantization.Fermionic.create j (basisState n)) +
          SecondQuantization.Fermionic.create j (B (basisState n)) =
        if i = j then basisState n else 0) :
    B = SecondQuantization.Fermionic.annihilate i := by
  apply linearMap_ext_basisState
  intro n
  induction n using Finset.induction with
  | empty =>
      simpa using hVac
  | @insert j n hj ih =>
      have hrecover :
          basisState (insert j n) =
            (fermionSign j n : ℂ) •
              SecondQuantization.Fermionic.create j (basisState n) := by
        rw [SecondQuantization.Fermionic.create_basisState_of_not_mem hj,
          smul_smul, fermionSign_sq_complex, one_smul]
      rw [hrecover, map_smul, map_smul]
      congr 1
      have hB := hCAR j n
      have hA := anticomm_annihilate_create_basisState i j n
      rw [anticomm_apply] at hA
      calc
        B (SecondQuantization.Fermionic.create j (basisState n)) =
            (if i = j then basisState n else 0) -
              SecondQuantization.Fermionic.create j (B (basisState n)) := by
          exact eq_sub_of_add_eq hB
        _ = (if i = j then basisState n else 0) -
              SecondQuantization.Fermionic.create j
                (SecondQuantization.Fermionic.annihilate i (basisState n)) := by
          rw [ih]
        _ = SecondQuantization.Fermionic.annihilate i
              (SecondQuantization.Fermionic.create j (basisState n)) := by
          exact (eq_sub_of_add_eq hA).symm

/-- The contraction by the `i`th coordinate functional, transported to occupation Fock space. -/
noncomputable def occupationAnnihilateFromField
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  occupationConjugate b (annihilateDual 𝓗₁ (b.coord i))

/-- The transported coordinate contraction is the existing occupation annihilation operator. -/
theorem occupationAnnihilateFromField_eq_annihilate
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    occupationAnnihilateFromField b i =
      SecondQuantization.Fermionic.annihilate i := by
  apply eq_annihilate_of_vacuum_of_mixedCAR
  · simp [occupationAnnihilateFromField, occupationConjugate]
  · intro j n
    apply (occupationEquiv b).injective
    have hCreateBasis := occupationEquiv_create_basisState b j n
    have hCreateGeneral := LinearMap.congr_fun (occupationEquiv_create b j)
      (occupationAnnihilateFromField b i (basisState n))
    rw [map_add, if_apply, map_zero]
    rw [occupationEquiv_occupationConjugate_apply]
    rw [hCreateBasis]
    rw [hCreateGeneral]
    rw [occupationEquiv_occupationConjugate_apply]
    rw [annihilateDual_create_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]

/-- The basis-induced equivalence intertwines the full annihilation operators. -/
theorem occupationEquiv_annihilate
    (b : Module.Basis Mode ℂ 𝓗₁) (i : Mode) :
    (occupationEquiv b).toLinearMap.comp
        SecondQuantization.Fermionic.annihilate i =
      (annihilateDual 𝓗₁ (b.coord i)).comp
        (occupationEquiv b).toLinearMap := by
  have h := occupationAnnihilateFromField_eq_annihilate b i
  apply LinearMap.ext
  intro Ψ
  have hApply := LinearMap.congr_fun h Ψ
  apply (occupationEquiv b).symm.injective
  simpa [occupationAnnihilateFromField, occupationConjugate,
    LinearMap.comp_apply] using congrArg (occupationEquiv b) hApply

end
end Field
end Fermionic
end SecondQuantization
