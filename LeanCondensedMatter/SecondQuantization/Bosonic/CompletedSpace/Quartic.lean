import LeanCondensedMatter.Analysis.Operator.Unbounded.Composition
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Ladder
import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic

set_option linter.style.header false

/-!
# Completed bosonic quartic vertices

This file gives the ordered number-conserving quartic monomial

`a†_{create₁} a†_{create₂} a_{annihilate₂} a_{annihilate₁}`

a genuine meaning on completed bosonic Fock space.  The four unbounded ladder operators are composed
with the exact `LinearPMap.compOnDomain` domain at every stage, so no operator product is formed outside the
domain on which the preceding result lies in the next operator's domain.

This is the first completed-space interacting operator.  The present file deliberately does not
replace the exact composition domain by a closed-form weighted `ℓ²` description, nor does it yet
form finite sums of quartic vertices.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- The ordered bosonic quartic vertex as a partially defined linear operator on completed Fock
space.  Its domain is the exact iterated composition domain of the four ladder operators. -/
noncomputable def completedQuarticVertexOperator (q : Common.QuarticVertexLabel Mode) :
    CompletedFockSpace Mode →ₗ.[ℂ] CompletedFockSpace Mode :=
  (completedCreate q.create₁).compOnDomain
    ((completedCreate q.create₂).compOnDomain
      ((completedAnnihilate q.annihilate₂).compOnDomain
        (completedAnnihilate q.annihilate₁)))


private theorem algebraicToCompleted_mem_completedCreateDomain
    (i : Mode) (x : FockSpace Mode) :
    algebraicToCompleted x ∈ (completedCreate i).domain := by
  change Common.algebraicToCompleted x ∈
    Common.completedDiagonalDomain
      (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ))
  exact Common.algebraicToCompleted_mem_completedDiagonalDomain _ x

private theorem algebraicToCompleted_mem_completedAnnihilateDomain
    (i : Mode) (x : FockSpace Mode) :
    algebraicToCompleted x ∈ (completedAnnihilate i).domain := by
  change Common.algebraicToCompleted x ∈
    Common.completedDiagonalDomain
      (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ))
  exact Common.algebraicToCompleted_mem_completedDiagonalDomain _ x

private theorem completedCreate_algebraicToCompleted
    (i : Mode) (x : FockSpace Mode)
    (h : algebraicToCompleted x ∈ (completedCreate i).domain) :
    completedCreate i ⟨algebraicToCompleted x, h⟩ =
      algebraicToCompleted (create i x) := by
  have hcore :=
    congrArg (fun f : FockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode => f x)
      (completedCreate_comp_algebraicCore i)
  have hcore' :
      (completedCreate i).toFun
          (Common.algebraicToCompletedDiagonalDomain
            (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ)) x) =
        algebraicToCompleted (create i x) := by
    simpa only [LinearMap.comp_apply] using hcore
  have hdomain :
      Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ)) x =
        ⟨algebraicToCompleted x, h⟩ := by
    apply Subtype.ext
    rfl
  rw [hdomain] at hcore'
  exact hcore'

private theorem completedAnnihilate_algebraicToCompleted
    (i : Mode) (x : FockSpace Mode)
    (h : algebraicToCompleted x ∈ (completedAnnihilate i).domain) :
    completedAnnihilate i ⟨algebraicToCompleted x, h⟩ =
      algebraicToCompleted (annihilate i x) := by
  have hcore :=
    congrArg (fun f : FockSpace Mode →ₗ[ℂ] CompletedFockSpace Mode => f x)
      (completedAnnihilate_comp_algebraicCore i)
  have hcore' :
      (completedAnnihilate i).toFun
          (Common.algebraicToCompletedDiagonalDomain
            (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ)) x) =
        algebraicToCompleted (annihilate i x) := by
    simpa only [LinearMap.comp_apply] using hcore
  have hdomain :
      Common.algebraicToCompletedDiagonalDomain
          (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ)) x =
        ⟨algebraicToCompleted x, h⟩ := by
    apply Subtype.ext
    rfl
  rw [hdomain] at hcore'
  exact hcore'

private theorem completedQuarticVertexOperator_algebraicCore_aux
    (q : Common.QuarticVertexLabel Mode) (x : FockSpace Mode) :
    ∃ h : algebraicToCompleted x ∈ (completedQuarticVertexOperator q).domain,
      completedQuarticVertexOperator q ⟨algebraicToCompleted x, h⟩ =
        algebraicToCompleted (Common.quarticVertexOperator create annihilate q x) := by
  let x1 := annihilate q.annihilate₁ x
  let x2 := annihilate q.annihilate₂ x1
  let x3 := create q.create₂ x2
  let p1 :=
    (completedAnnihilate q.annihilate₂).compOnDomain
      (completedAnnihilate q.annihilate₁)
  let p2 :=
    (completedCreate q.create₂).compOnDomain p1

  have h1 :
      algebraicToCompleted x ∈ (completedAnnihilate q.annihilate₁).domain :=
    algebraicToCompleted_mem_completedAnnihilateDomain q.annihilate₁ x
  have h1_apply :
      completedAnnihilate q.annihilate₁ ⟨algebraicToCompleted x, h1⟩ =
        algebraicToCompleted x1 := by
    simpa [x1] using
      completedAnnihilate_algebraicToCompleted q.annihilate₁ x h1

  have h2core :
      algebraicToCompleted x1 ∈ (completedAnnihilate q.annihilate₂).domain :=
    algebraicToCompleted_mem_completedAnnihilateDomain q.annihilate₂ x1
  have h2 :
      completedAnnihilate q.annihilate₁ ⟨algebraicToCompleted x, h1⟩ ∈
        (completedAnnihilate q.annihilate₂).domain := by
    rw [h1_apply]
    exact h2core
  have hp1 : algebraicToCompleted x ∈ p1.domain := by
    apply (LinearPMap.mem_compOnDomain_domain_iff
      (completedAnnihilate q.annihilate₂)
      (completedAnnihilate q.annihilate₁) _).2
    exact ⟨h1, h2⟩
  have hp1_apply :
      p1 ⟨algebraicToCompleted x, hp1⟩ = algebraicToCompleted x2 := by
    change
      (completedAnnihilate q.annihilate₂).compOnDomain
          (completedAnnihilate q.annihilate₁)
          ⟨algebraicToCompleted x, hp1⟩ =
        algebraicToCompleted x2
    rw [LinearPMap.compOnDomain_apply
      (completedAnnihilate q.annihilate₂)
      (completedAnnihilate q.annihilate₁) hp1 h1 h2]
    have hinner :
        (⟨completedAnnihilate q.annihilate₁
              ⟨algebraicToCompleted x, h1⟩, h2⟩ :
            (completedAnnihilate q.annihilate₂).domain) =
          ⟨algebraicToCompleted x1, h2core⟩ := by
      apply Subtype.ext
      exact h1_apply
    rw [hinner]
    simpa [x2] using
      completedAnnihilate_algebraicToCompleted q.annihilate₂ x1 h2core

  have h3core :
      algebraicToCompleted x2 ∈ (completedCreate q.create₂).domain :=
    algebraicToCompleted_mem_completedCreateDomain q.create₂ x2
  have h3 :
      p1 ⟨algebraicToCompleted x, hp1⟩ ∈
        (completedCreate q.create₂).domain := by
    rw [hp1_apply]
    exact h3core
  have hp2 : algebraicToCompleted x ∈ p2.domain := by
    apply (LinearPMap.mem_compOnDomain_domain_iff
      (completedCreate q.create₂) p1 _).2
    exact ⟨hp1, h3⟩
  have hp2_apply :
      p2 ⟨algebraicToCompleted x, hp2⟩ = algebraicToCompleted x3 := by
    change
      (completedCreate q.create₂).compOnDomain p1
          ⟨algebraicToCompleted x, hp2⟩ =
        algebraicToCompleted x3
    rw [LinearPMap.compOnDomain_apply (completedCreate q.create₂) p1 hp2 hp1 h3]
    have hinner :
        (⟨p1 ⟨algebraicToCompleted x, hp1⟩, h3⟩ :
            (completedCreate q.create₂).domain) =
          ⟨algebraicToCompleted x2, h3core⟩ := by
      apply Subtype.ext
      exact hp1_apply
    rw [hinner]
    simpa [x3] using
      completedCreate_algebraicToCompleted q.create₂ x2 h3core

  have h4core :
      algebraicToCompleted x3 ∈ (completedCreate q.create₁).domain :=
    algebraicToCompleted_mem_completedCreateDomain q.create₁ x3
  have h4 :
      p2 ⟨algebraicToCompleted x, hp2⟩ ∈
        (completedCreate q.create₁).domain := by
    rw [hp2_apply]
    exact h4core
  have hq :
      algebraicToCompleted x ∈
        ((completedCreate q.create₁).compOnDomain p2).domain := by
    apply (LinearPMap.mem_compOnDomain_domain_iff
      (completedCreate q.create₁) p2 _).2
    exact ⟨hp2, h4⟩
  refine ⟨?_, ?_⟩
  · simpa [completedQuarticVertexOperator, p1, p2] using hq
  · change
      (completedCreate q.create₁).compOnDomain p2
          ⟨algebraicToCompleted x, hq⟩ =
        algebraicToCompleted (Common.quarticVertexOperator create annihilate q x)
    rw [LinearPMap.compOnDomain_apply (completedCreate q.create₁) p2 hq hp2 h4]
    have hinner :
        (⟨p2 ⟨algebraicToCompleted x, hp2⟩, h4⟩ :
            (completedCreate q.create₁).domain) =
          ⟨algebraicToCompleted x3, h4core⟩ := by
      apply Subtype.ext
      exact hp2_apply
    rw [hinner]
    have h4_apply :=
      completedCreate_algebraicToCompleted q.create₁ x3 h4core
    simpa [Common.quarticVertexOperator, LinearMap.comp_apply, x1, x2, x3] using h4_apply

/-- Every finite-support algebraic bosonic Fock vector lies in the exact domain of every completed
quartic vertex. -/
theorem algebraicToCompleted_mem_completedQuarticVertexOperator_domain
    (q : Common.QuarticVertexLabel Mode) (x : FockSpace Mode) :
    algebraicToCompleted x ∈ (completedQuarticVertexOperator q).domain :=
  (completedQuarticVertexOperator_algebraicCore_aux q x).choose

/-- The completed quartic vertex agrees with the algebraic quartic vertex on the finite-support
core. -/
theorem completedQuarticVertexOperator_algebraicCore
    (q : Common.QuarticVertexLabel Mode) (x : FockSpace Mode) :
    completedQuarticVertexOperator q
        ⟨algebraicToCompleted x,
          algebraicToCompleted_mem_completedQuarticVertexOperator_domain q x⟩ =
      algebraicToCompleted (Common.quarticVertexOperator create annihilate q x) := by
  exact (completedQuarticVertexOperator_algebraicCore_aux q x).choose_spec

/-- The exact domain of every completed quartic vertex is dense. -/
theorem completedQuarticVertexOperator_denseDomain
    (q : Common.QuarticVertexLabel Mode) :
    Dense (((completedQuarticVertexOperator q).domain :
      Submodule ℂ (CompletedFockSpace Mode)) : Set (CompletedFockSpace Mode)) := by
  apply Dense.mono ?_ (by
    simpa [algebraicToCompleted] using
      (Common.algebraicToCompleted_denseRange (Config := Occupation Mode)))
  rintro _ ⟨x, rfl⟩
  exact algebraicToCompleted_mem_completedQuarticVertexOperator_domain q x

end
end Bosonic
end SecondQuantization
