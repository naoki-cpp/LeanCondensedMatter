import LeanCondensedMatter.Combinatorics.FamilySlotShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoComponentOrderedSimplex

set_option linter.style.header false

/-!
# Finite-family presentations of diagram component shuffles

After enumerating the connected-component blocks by `Fin k`, a diagram `ComponentShuffle` is
exactly a `FamilySlotShuffle` for the corresponding family of component sizes. This module
constructs that equivalence and identifies the associated shuffled ordered-simplex integrands and
finite sums.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- An enumeration of all connected-component blocks of a diagram by `Fin k`. -/
structure QuarticDiagram.FiniteComponentPresentation {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (k : ℕ) where
  partsEquiv : Fin k ≃ d.componentPartition.parts

/-- The canonical finite presentation obtained by enumerating the component type. -/
noncomputable def QuarticDiagram.FiniteComponentPresentation.canonical
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) :
    d.FiniteComponentPresentation (Fintype.card d.componentPartition.parts) where
  partsEquiv := (Fintype.equivFin d.componentPartition.parts).symm

/-- Number of local vertex slots in the component with index `i`. -/
abbrev QuarticDiagram.FiniteComponentPresentation.size
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) (i : Fin k) : ℕ :=
  (p.partsEquiv i : Finset (Fin N)).card

/-- Reindex the sigma type of finite-family local slots by the chosen component enumeration. -/
noncomputable def QuarticDiagram.FiniteComponentPresentation.localSlotEquiv
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) :
    (Σ i : Fin k, Fin (p.size i)) ≃
      (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) :=
  p.partsEquiv.sigmaCongrLeft
    (β := fun B : d.componentPartition.parts => Fin (B : Finset (Fin N)).card)

@[simp]
theorem QuarticDiagram.FiniteComponentPresentation.localSlotEquiv_apply
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) (i : Fin k) (j : Fin (p.size i)) :
    p.localSlotEquiv ⟨i, j⟩ = ⟨p.partsEquiv i, j⟩ := by
  simp [QuarticDiagram.FiniteComponentPresentation.localSlotEquiv]

@[simp]
theorem QuarticDiagram.FiniteComponentPresentation.localSlotEquiv_symm_apply
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) (i : Fin k) (j : Fin (p.size i)) :
    p.localSlotEquiv.symm ⟨p.partsEquiv i, j⟩ = ⟨i, j⟩ := by
  apply p.localSlotEquiv.injective
  simp

/-- The sum of the enumerated component sizes is the global number of vertices. -/
theorem QuarticDiagram.FiniteComponentPresentation.totalCard
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) : (∑ i, p.size i) = S.card := by
  classical
  calc
    (∑ i, p.size i) =
        ∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card := by
      simpa [Fintype.card_sigma] using Fintype.card_congr p.localSlotEquiv
    _ = S.card := by
      rw [Finset.sum_coe_sort]
      exact d.componentPartition.sum_card_parts

/-- Transport a finite-family slot shuffle to a diagram component shuffle. -/
noncomputable def QuarticDiagram.FiniteComponentPresentation.toComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k)
    (shuffle : FamilySlotShuffle p.size) : d.ComponentShuffle where
  slotEquiv := p.localSlotEquiv.symm.trans
    (shuffle.slotEquiv.trans (finCongr p.totalCard))
  strictMono := by
    intro B
    obtain ⟨i, rfl⟩ := p.partsEquiv.surjective B
    intro a b hab
    change (finCongr p.totalCard)
        (shuffle.slotEquiv (p.localSlotEquiv.symm ⟨p.partsEquiv i, a⟩)) <
      (finCongr p.totalCard)
        (shuffle.slotEquiv (p.localSlotEquiv.symm ⟨p.partsEquiv i, b⟩))
    rw [p.localSlotEquiv_symm_apply, p.localSlotEquiv_symm_apply]
    exact (strictMono_finCongr p.totalCard) (shuffle.strictMono i hab)

/-- Read a finite-family slot shuffle from a diagram component shuffle. -/
noncomputable def QuarticDiagram.FiniteComponentPresentation.fromComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) (shuffle : d.ComponentShuffle) :
    FamilySlotShuffle p.size where
  slotEquiv := p.localSlotEquiv.trans
    (shuffle.slotEquiv.trans (finCongr p.totalCard).symm)
  strictMono := by
    intro i a b hab
    have hcast : StrictMono (finCongr p.totalCard).symm := by
      simpa using strictMono_finCongr p.totalCard.symm
    change (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv ⟨i, a⟩)) <
      (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv ⟨i, b⟩))
    rw [p.localSlotEquiv_apply, p.localSlotEquiv_apply]
    exact hcast (shuffle.strictMono (p.partsEquiv i) hab)

/-- Finite-family slot shuffles and diagram component shuffles are equivalent after enumerating all
component blocks. -/
noncomputable def QuarticDiagram.FiniteComponentPresentation.componentShuffleEquiv
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) :
    FamilySlotShuffle p.size ≃ d.ComponentShuffle where
  toFun := p.toComponentShuffle
  invFun := p.fromComponentShuffle
  left_inv shuffle := by
    apply FamilySlotShuffle.ext
    ext x
    simp [QuarticDiagram.FiniteComponentPresentation.toComponentShuffle,
      QuarticDiagram.FiniteComponentPresentation.fromComponentShuffle]
  right_inv shuffle := by
    apply QuarticDiagram.ComponentShuffle.ext
    ext x
    simp [QuarticDiagram.FiniteComponentPresentation.toComponentShuffle,
      QuarticDiagram.FiniteComponentPresentation.fromComponentShuffle]

/-- The component-shuffle integrand transported from a finite-family shuffle is the generic family
integrand, with only the global finite-dimension cast remaining. -/
theorem QuarticDiagram.FiniteComponentPresentation.componentShuffleIntegrand_toComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) (shuffle : FamilySlotShuffle p.size)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) :
    d.componentShuffleIntegrand (p.toComponentShuffle shuffle) componentIntegrand τ =
      shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))
        (fun j => τ (finCongr p.totalCard j)) := by
  classical
  unfold QuarticDiagram.componentShuffleIntegrand FamilySlotShuffle.integrand
  calc
    (∏ B : d.componentPartition.parts,
        componentIntegrand B
          (d.componentTimeAssignment (p.toComponentShuffle shuffle) τ B)) =
      ∏ i : Fin k,
        componentIntegrand (p.partsEquiv i)
          (d.componentTimeAssignment (p.toComponentShuffle shuffle) τ (p.partsEquiv i)) := by
        symm
        refine Fintype.prod_equiv p.partsEquiv _ _ ?_
        intro i
        rfl
    _ = ∏ i : Fin k,
        componentIntegrand (p.partsEquiv i)
          (shuffle.timeAssignment (fun j => τ (finCongr p.totalCard j)) i) := by
        apply congrArg (fun h : Fin k → ℂ => ∏ i, h i)
        funext i
        apply congrArg (componentIntegrand (p.partsEquiv i))
        funext j
        simp [QuarticDiagram.componentTimeAssignment,
          QuarticDiagram.FiniteComponentPresentation.toComponentShuffle,
          FamilySlotShuffle.timeAssignment]

/-- One transported component-shuffle ordered-simplex term is the corresponding generic
finite-family term. -/
theorem QuarticDiagram.FiniteComponentPresentation.orderedSimplexIntegral_toComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) (shuffle : FamilySlotShuffle p.size)
    (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ) :
    orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand (p.toComponentShuffle shuffle) componentIntegrand) =
      orderedSimplexIntegral (∑ i, p.size i) β
        (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) := by
  calc
    orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand (p.toComponentShuffle shuffle) componentIntegrand) =
      orderedSimplexIntegral S.card β (fun τ =>
        shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))
          (fun j => τ (finCongr p.totalCard j))) := by
            apply orderedSimplexIntegral_congr
            intro τ
            exact p.componentShuffleIntegrand_toComponentShuffle shuffle componentIntegrand τ
    _ = orderedSimplexIntegral (∑ i, p.size i) β
        (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) := by
          symm
          simpa using intervalIntegral.orderedSimplexIntegral_cast p.totalCard β
            (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i)))

/-- Reindex the finite sum over diagram component shuffles as a sum over generic finite-family
shuffles. -/
theorem QuarticDiagram.FiniteComponentPresentation.sum_componentShuffle_orderedSimplexIntegral
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S} {k : ℕ}
    (p : d.FiniteComponentPresentation k) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ) :
    (∑ shuffle : d.ComponentShuffle,
      orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand shuffle componentIntegrand)) =
      ∑ shuffle : FamilySlotShuffle p.size,
        orderedSimplexIntegral (∑ i, p.size i) β
          (shuffle.integrand (fun i => componentIntegrand (p.partsEquiv i))) := by
  rw [← Equiv.sum_comp p.componentShuffleEquiv]
  apply Finset.sum_congr rfl
  intro shuffle _hshuffle
  change orderedSimplexIntegral S.card β
      (d.componentShuffleIntegrand (p.toComponentShuffle shuffle) componentIntegrand) = _
  exact p.orderedSimplexIntegral_toComponentShuffle shuffle β componentIntegrand

end Common
end SecondQuantization
