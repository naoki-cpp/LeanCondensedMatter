import LeanCondensedMatter.Analysis.BinaryShuffleSlotOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrderedSimplex
import Mathlib.Logic.Equiv.Sum

set_option linter.style.header false

/-!
# Two-component diagram shuffles

A binary ambient slot shuffle and a component shuffle are the same object once the two component
blocks have been enumerated. This module packages that enumeration, transports the shuffle in both
directions, identifies the corresponding component-shuffle integrand, and specializes the binary
ordered-simplex product formula to a diagram with two named components.
-/

namespace SecondQuantization
namespace Common

open intervalIntegral
open Combinatorics BinaryShuffle

variable {Label : Type*} {N : ℕ}

/-- An enumeration of the connected-component blocks of a diagram by `Bool`. The `false` component
is regarded as the left block and the `true` component as the right block. -/
structure QuarticDiagram.TwoComponentPresentation {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) where
  partsEquiv : Bool ≃ d.componentPartition.parts

/-- A two-component presentation exists whenever the component type has cardinality two. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.ofCardTwo
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S)
    (hcard : Fintype.card d.componentPartition.parts = 2) :
    d.TwoComponentPresentation where
  partsEquiv := Fintype.equivOfCardEq (by simpa [hcard])

/-- The component assigned to the left factor. -/
def QuarticDiagram.TwoComponentPresentation.leftComponent
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) : d.componentPartition.parts :=
  p.partsEquiv false

/-- The component assigned to the right factor. -/
def QuarticDiagram.TwoComponentPresentation.rightComponent
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) : d.componentPartition.parts :=
  p.partsEquiv true

/-- Number of local vertex slots in the left component. -/
abbrev QuarticDiagram.TwoComponentPresentation.leftSize
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) : ℕ :=
  (p.leftComponent : Finset (Fin N)).card

/-- Number of local vertex slots in the right component. -/
abbrev QuarticDiagram.TwoComponentPresentation.rightSize
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) : ℕ :=
  (p.rightComponent : Finset (Fin N)).card

/-- Identify the local slot fiber over a Boolean component with the corresponding left/right fiber. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.boolSlotFiberEquiv
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (b : Bool) :
    Fin ((p.partsEquiv b : d.componentPartition.parts) : Finset (Fin N)).card ≃
      bif b then Fin p.rightSize else Fin p.leftSize := by
  cases b <;> exact Equiv.refl _

/-- Reindex a Boolean sigma family by the chosen component enumeration. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.partsSigmaEquiv
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) :
    (Σ b : Bool,
      Fin ((p.partsEquiv b : d.componentPartition.parts) : Finset (Fin N)).card) ≃
      (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) :=
  p.partsEquiv.sigmaCongrLeft

/-- Embed a binary sum of the two local slot families into the sigma type of all component-local
slots. This direction computes directly on `Sum.inl` and `Sum.inr`. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.sumToLocalSlotEquiv
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) :
    Fin p.leftSize ⊕ Fin p.rightSize ≃
      (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) :=
  (Equiv.sumEquivSigmaBool (Fin p.leftSize) (Fin p.rightSize)).trans
    ((Equiv.sigmaCongrRight fun b => (p.boolSlotFiberEquiv b).symm).trans
      p.partsSigmaEquiv)

@[simp]
theorem QuarticDiagram.TwoComponentPresentation.sumToLocalSlotEquiv_inl
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (i : Fin p.leftSize) :
    p.sumToLocalSlotEquiv (Sum.inl i) = ⟨p.leftComponent, i⟩ := by
  simp [QuarticDiagram.TwoComponentPresentation.sumToLocalSlotEquiv,
    QuarticDiagram.TwoComponentPresentation.partsSigmaEquiv,
    QuarticDiagram.TwoComponentPresentation.boolSlotFiberEquiv,
    QuarticDiagram.TwoComponentPresentation.leftComponent]

@[simp]
theorem QuarticDiagram.TwoComponentPresentation.sumToLocalSlotEquiv_inr
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (i : Fin p.rightSize) :
    p.sumToLocalSlotEquiv (Sum.inr i) = ⟨p.rightComponent, i⟩ := by
  simp [QuarticDiagram.TwoComponentPresentation.sumToLocalSlotEquiv,
    QuarticDiagram.TwoComponentPresentation.partsSigmaEquiv,
    QuarticDiagram.TwoComponentPresentation.boolSlotFiberEquiv,
    QuarticDiagram.TwoComponentPresentation.rightComponent]

/-- Identify the sigma type of all component-local slots with a binary sum of the two local slot
families. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.localSlotEquiv
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) :
    (Σ B : d.componentPartition.parts, Fin (B : Finset (Fin N)).card) ≃
      Fin p.leftSize ⊕ Fin p.rightSize :=
  p.sumToLocalSlotEquiv.symm

@[simp]
theorem QuarticDiagram.TwoComponentPresentation.localSlotEquiv_left
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (i : Fin p.leftSize) :
    p.localSlotEquiv ⟨p.leftComponent, i⟩ = Sum.inl i := by
  apply p.sumToLocalSlotEquiv.injective
  simp [QuarticDiagram.TwoComponentPresentation.localSlotEquiv]

@[simp]
theorem QuarticDiagram.TwoComponentPresentation.localSlotEquiv_right
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (i : Fin p.rightSize) :
    p.localSlotEquiv ⟨p.rightComponent, i⟩ = Sum.inr i := by
  apply p.sumToLocalSlotEquiv.injective
  simp [QuarticDiagram.TwoComponentPresentation.localSlotEquiv]

@[simp]
theorem QuarticDiagram.TwoComponentPresentation.localSlotEquiv_symm_inl
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (i : Fin p.leftSize) :
    p.localSlotEquiv.symm (Sum.inl i) = ⟨p.leftComponent, i⟩ := by
  exact p.sumToLocalSlotEquiv_inl i

@[simp]
theorem QuarticDiagram.TwoComponentPresentation.localSlotEquiv_symm_inr
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (i : Fin p.rightSize) :
    p.localSlotEquiv.symm (Sum.inr i) = ⟨p.rightComponent, i⟩ := by
  exact p.sumToLocalSlotEquiv_inr i

/-- The two local component sizes add up to the global number of vertices. -/
theorem QuarticDiagram.TwoComponentPresentation.totalCard
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) : p.leftSize + p.rightSize = S.card := by
  classical
  have hslots :
      (∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card) =
        p.leftSize + p.rightSize := by
    simpa [Fintype.card_sigma] using Fintype.card_congr p.localSlotEquiv
  calc
    p.leftSize + p.rightSize =
        ∑ B : d.componentPartition.parts, (B : Finset (Fin N)).card := hslots.symm
    _ = S.card := by
      rw [Finset.sum_coe_sort]
      exact d.componentPartition.sum_card_parts

/-- Casting between equal finite dimensions preserves strict order. -/
theorem strictMono_finCongr {a b : ℕ} (h : a = b) : StrictMono (finCongr h) := by
  subst b
  simpa using (strictMono_id : StrictMono (fun i : Fin a => i))

/-- Transport a binary ambient slot shuffle to the component-local sigma type. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.toComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation)
    (shuffle : SlotShuffle p.leftSize p.rightSize) : d.ComponentShuffle where
  slotEquiv := p.localSlotEquiv.trans
    (shuffle.slotEquiv.trans (finCongr p.totalCard))
  strictMono := by
    intro B
    obtain ⟨b, rfl⟩ := p.partsEquiv.surjective B
    cases b with
    | false =>
        intro i j hij
        change (finCongr p.totalCard)
            (shuffle.slotEquiv (p.localSlotEquiv ⟨p.leftComponent, i⟩)) <
          (finCongr p.totalCard)
            (shuffle.slotEquiv (p.localSlotEquiv ⟨p.leftComponent, j⟩))
        rw [p.localSlotEquiv_left, p.localSlotEquiv_left]
        exact (strictMono_finCongr p.totalCard) (shuffle.strictMonoLeft hij)
    | true =>
        intro i j hij
        change (finCongr p.totalCard)
            (shuffle.slotEquiv (p.localSlotEquiv ⟨p.rightComponent, i⟩)) <
          (finCongr p.totalCard)
            (shuffle.slotEquiv (p.localSlotEquiv ⟨p.rightComponent, j⟩))
        rw [p.localSlotEquiv_right, p.localSlotEquiv_right]
        exact (strictMono_finCongr p.totalCard) (shuffle.strictMonoRight hij)

/-- Read a binary ambient slot shuffle from a component shuffle under a two-component presentation. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.fromComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (shuffle : d.ComponentShuffle) :
    SlotShuffle p.leftSize p.rightSize where
  slotEquiv := p.localSlotEquiv.symm.trans
    (shuffle.slotEquiv.trans (finCongr p.totalCard).symm)
  strictMonoLeft := by
    intro i j hij
    have hcast : StrictMono (finCongr p.totalCard).symm := by
      simpa using strictMono_finCongr p.totalCard.symm
    change (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv.symm (Sum.inl i))) <
      (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv.symm (Sum.inl j)))
    rw [p.localSlotEquiv_symm_inl, p.localSlotEquiv_symm_inl]
    exact hcast ((shuffle.strictMono p.leftComponent) hij)
  strictMonoRight := by
    intro i j hij
    have hcast : StrictMono (finCongr p.totalCard).symm := by
      simpa using strictMono_finCongr p.totalCard.symm
    change (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv.symm (Sum.inr i))) <
      (finCongr p.totalCard).symm
        (shuffle.slotEquiv (p.localSlotEquiv.symm (Sum.inr j)))
    rw [p.localSlotEquiv_symm_inr, p.localSlotEquiv_symm_inr]
    exact hcast ((shuffle.strictMono p.rightComponent) hij)

/-- Binary slot shuffles and component shuffles are equivalent after choosing the two component
blocks. -/
noncomputable def QuarticDiagram.TwoComponentPresentation.componentShuffleEquiv
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) :
    SlotShuffle p.leftSize p.rightSize ≃ d.ComponentShuffle where
  toFun := p.toComponentShuffle
  invFun := p.fromComponentShuffle
  left_inv shuffle := by
    apply SlotShuffle.ext
    apply Equiv.ext
    intro x
    simp [QuarticDiagram.TwoComponentPresentation.toComponentShuffle,
      QuarticDiagram.TwoComponentPresentation.fromComponentShuffle]
  right_inv shuffle := by
    apply QuarticDiagram.ComponentShuffle.ext
    apply Equiv.ext
    intro x
    simp [QuarticDiagram.TwoComponentPresentation.toComponentShuffle,
      QuarticDiagram.TwoComponentPresentation.fromComponentShuffle]

@[simp]
theorem QuarticDiagram.TwoComponentPresentation.componentShuffleEquiv_apply
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (shuffle : SlotShuffle p.leftSize p.rightSize) :
    p.componentShuffleEquiv shuffle = p.toComponentShuffle shuffle :=
  rfl

/-- The diagram component-shuffle integrand transported from a binary shuffle is the ordinary binary
ambient-slot integrand, with only the global dimension cast remaining. -/
theorem QuarticDiagram.TwoComponentPresentation.componentShuffleIntegrand_toComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (shuffle : SlotShuffle p.leftSize p.rightSize)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (τ : Fin S.card → ℝ) :
    d.componentShuffleIntegrand (p.toComponentShuffle shuffle) componentIntegrand τ =
      shuffle.integrand (componentIntegrand p.leftComponent)
        (componentIntegrand p.rightComponent)
        (fun i => τ (finCongr p.totalCard i)) := by
  classical
  unfold QuarticDiagram.componentShuffleIntegrand SlotShuffle.integrand
  calc
    (∏ B : d.componentPartition.parts,
        componentIntegrand B
          (d.componentTimeAssignment (p.toComponentShuffle shuffle) τ B)) =
      ∏ b : Bool,
        componentIntegrand (p.partsEquiv b)
          (d.componentTimeAssignment (p.toComponentShuffle shuffle) τ (p.partsEquiv b)) := by
        symm
        refine Fintype.prod_equiv p.partsEquiv _ _ ?_
        intro b
        rfl
    _ = componentIntegrand p.leftComponent
          (d.componentTimeAssignment (p.toComponentShuffle shuffle) τ p.leftComponent) *
        componentIntegrand p.rightComponent
          (d.componentTimeAssignment (p.toComponentShuffle shuffle) τ p.rightComponent) := by
        simpa [QuarticDiagram.TwoComponentPresentation.leftComponent,
          QuarticDiagram.TwoComponentPresentation.rightComponent, mul_comm]
    _ = componentIntegrand p.leftComponent
          (fun i => τ (finCongr p.totalCard (shuffle.slotEquiv (Sum.inl i)))) *
        componentIntegrand p.rightComponent
          (fun i => τ (finCongr p.totalCard (shuffle.slotEquiv (Sum.inr i)))) := by
        apply congrArg₂ (· * ·)
        · apply congrArg (componentIntegrand p.leftComponent)
          funext i
          simp [QuarticDiagram.componentTimeAssignment,
            QuarticDiagram.TwoComponentPresentation.toComponentShuffle]
        · apply congrArg (componentIntegrand p.rightComponent)
          funext i
          simp [QuarticDiagram.componentTimeAssignment,
            QuarticDiagram.TwoComponentPresentation.toComponentShuffle]

/-- One transported component-shuffle ordered-simplex term is the corresponding binary ambient-slot
term. -/
theorem QuarticDiagram.TwoComponentPresentation.orderedSimplexIntegral_toComponentShuffle
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (shuffle : SlotShuffle p.leftSize p.rightSize)
    (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ) :
    orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand (p.toComponentShuffle shuffle) componentIntegrand) =
      orderedSimplexIntegral (p.leftSize + p.rightSize) β
        (shuffle.integrand (componentIntegrand p.leftComponent)
          (componentIntegrand p.rightComponent)) := by
  calc
    orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand (p.toComponentShuffle shuffle) componentIntegrand) =
      orderedSimplexIntegral S.card β (fun τ =>
        shuffle.integrand (componentIntegrand p.leftComponent)
          (componentIntegrand p.rightComponent)
          (fun i => τ (finCongr p.totalCard i))) := by
            apply orderedSimplexIntegral_congr
            intro τ
            exact p.componentShuffleIntegrand_toComponentShuffle shuffle componentIntegrand τ
    _ = orderedSimplexIntegral (p.leftSize + p.rightSize) β
        (shuffle.integrand (componentIntegrand p.leftComponent)
          (componentIntegrand p.rightComponent)) := by
          symm
          simpa using BinaryShuffle.orderedSimplexIntegral_cast p.totalCard β
            (shuffle.integrand (componentIntegrand p.leftComponent)
              (componentIntegrand p.rightComponent))

/-- Two-component specialization of the component-shuffle ordered-simplex product formula. -/
theorem QuarticDiagram.TwoComponentPresentation.sum_componentShuffle_orderedSimplexIntegral_eq_mul
    {S : Finset (Fin N)} {d : QuarticDiagram Label N S}
    (p : d.TwoComponentPresentation) (β : ℝ)
    (componentIntegrand :
      ∀ B : d.componentPartition.parts, (Fin (B : Finset (Fin N)).card → ℝ) → ℂ)
    (hcomponent : ∀ B, Continuous (componentIntegrand B)) :
    (∑ shuffle : d.ComponentShuffle,
      orderedSimplexIntegral S.card β
        (d.componentShuffleIntegrand shuffle componentIntegrand)) =
      orderedSimplexIntegral p.leftSize β (componentIntegrand p.leftComponent) *
        orderedSimplexIntegral p.rightSize β (componentIntegrand p.rightComponent) := by
  rw [← Equiv.sum_comp p.componentShuffleEquiv
    (fun shuffle => orderedSimplexIntegral S.card β
      (d.componentShuffleIntegrand shuffle componentIntegrand))]
  simp_rw [p.componentShuffleEquiv_apply,
    p.orderedSimplexIntegral_toComponentShuffle]
  exact BinaryShuffle.sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul
    p.leftSize p.rightSize β
    (componentIntegrand p.leftComponent) (componentIntegrand p.rightComponent)
    (hcomponent p.leftComponent) (hcomponent p.rightComponent)

end Common
end SecondQuantization
